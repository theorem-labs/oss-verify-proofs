(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from O14/O14ExitR23.v: ref_exit_clean, ref_exit_flush, ref_exit and ref_exit_Z restated over the budget carrier rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader premise of ref_exit_flush_b, which ref_exit_b takes from its flush case). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Kit O14_code_exitpath.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14ExitR23.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.BudgetWit Require Rzb ExitB.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O14ExitB.
Import O14Kit.O14ExitBase.
Import O14Kit.O14StdioDefs.
Import O14Kit.O14Reloc.
Import O14Kit.O14RelocCode.
Import O14Kit.O14RelocSites.
Import O14Kit.O14RelocImg.
Import O14Kit.O14RelocMusl.

Import O14ExitR23.O14Exit.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.BudgetWit.Rzb.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1.
  Context {fx : FPState}.
Theorem ref_exit_clean_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x2bbc0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  rzb RSEGS (mkCfg (mkst regs (0x21bbc : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct (w_pre regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC)
    as (regs1 & mem1 & RUN & Rsp & Rs0 & Rra & SOK1 & TR).
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
  destruct EC as [Esp Etp Ea0 Esplo Esphi Esok Etplo Etphi Etid Emtid Elock Efe Efs Efa Ecomp Eg1 Eg2 Eglob Eerr Edso Ealock Eatexit].
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  assert (G1 : stdio_globals mem1).
  { repeat split; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC1 : file_clean mem1 0x2bbc0 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x2bad0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@ExitB.exit_tail_clean_b fx o14_reloc o14_code o14_sites o14_data o14_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

Section VP2.
  Context {fx : FPState}.
Theorem ref_exit_flush_b :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  rzb RSEGS (mkCfg (mkst regs (0x21bbc : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrd.
  destruct (w_pre regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC)
    as (regs1 & mem1 & RUN & Rsp & Rs0 & Rra & SOK1 & TR).
  eapply rzb_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
  destruct EC as [Esp Etp Ea0 Esplo Esphi Esok Etplo Etphi Etid Emtid Elock Efe Efs Efa Ecomp Eg1 Eg2 Eglob Eerr Edso Ealock Eatexit].
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  assert (G1 : stdio_globals mem1).
  { repeat split; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x2bad0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@ExitB.exit_tail_flush_b fx o14_reloc o14_code o14_sites o14_data o14_rw
             regs1 mem1 model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending
             Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC2 (stdout_pending_G _ _ _ _ _ _ _ _ SP1) Hh Hlazy Hfd Hrd).
Qed.
End VP2.

Section VP4.
  Context {fx : FPState}.
Theorem ref_exit_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (0x21bbc : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(E & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrd)].
  - subst pending. cbn [W map].
    eapply rzb_conseq; [| apply t_emit_nil_exit].
    exact (ref_exit_clean_b regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy).
  - exact (ref_exit_flush_b regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrd).
Qed.
End VP4.

Section VP5.
  Context {fx : FPState}.
Corollary ref_exit_Z_b : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  rzb RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x21bbc) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x21bbc) with (0x21bbc : word) by (apply bv_eq; reflexivity).
  exact (ref_exit_b regs mem model code pending PRE).
Qed.
End VP5.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O14ExitB.
