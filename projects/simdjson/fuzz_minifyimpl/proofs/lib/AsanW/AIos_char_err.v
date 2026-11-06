(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit AImg MonadF AIos_tac AIos_iface AIos_char.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ITreeA StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section CharErr.
  Variable ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Hypothesis FW0E : fwrite0_err_stmt ICPT ICPTR.
  Hypothesis FFLE : fflush_err_stmt ICPT ICPTR.
  Hypothesis ICPT_frame : forall W m m', ICPT m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232)) W -> ICPT m'.

  Lemma sync_err_spec :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk asegs m lo (bv_unsigned sp) -> stderr_file m ->
      ssp_cells m guard -> ICPT m -> ios_char_shared m -> ios_clog m -> mem_inv asegs m ->
      a0 = Z_to_bv 64 0x6a2f28 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4176 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF asegs RNG (icpt_post ICPT [(bv_unsigned sp - 4176, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]
                                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m (fun m' => stderr_file m'))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x109afc) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros ST SEF SSP IC IOSS IOSC MI -> -> LO GLO ATL AL RSTK RIMG RI.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSS as (VB & SYNCV & CVP & UNSH). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4176, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 80%nat ST.
    steps_to 0x131380%Z.
    nstep. nstep. nstep.
    steps_to 0x6c248%Z.
    replace (bv_unsigned sp + -64 - (bv_unsigned sp + -64)) with 0 by (clear; lia).
    call_sp (FW0E RNG);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia)
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]]) ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    steps_to 0x6c2a8%Z.
    call_sp (FFLE RNG);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia) ].
    hstep. hstep. do 9 hstep.
    change (Z.b2z (0 <? 1) + -1) with 0.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -80)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evtF_done. unfold icpt_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; eassumption.
  Qed.

  Definition flush_err_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6a3398) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 4224, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m' /\ stderr_file m'.

  Lemma flush_err_spec :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word),
      stk asegs m lo (bv_unsigned sp) -> stderr_file m ->
      ssp_cells m guard -> ICPT m -> ios_char_shared m -> ios_clog m -> mem_inv asegs m ->
      a0 = Z_to_bv 64 0x6a3398 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4224 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG ->
      evtF asegs RNG (flush_err_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x108494) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros ST SEF SSP IC IOSS IOSC MI -> -> LO GLO ATL AL RSTK RIMG RI.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSS as (VB & SYNCV & CVP & UNSH). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4224, bv_unsigned sp); (RSTDERR, RSTDERR + 232)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    steps_to 0x109afc%Z.
    call_sp (sync_err_spec RNG);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia)
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]]) ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_char_shared. conj_by_addr. }
    { unfold ios_clog. conj_by_addr. }
    destruct POST as (eflags2 & emode2 & ee2 & ewend2 & etail2 & EFC2). unfold file_cells in EFC2.
    steps_to 0x108668%Z.
    match goal with S : stk _ _ lo (bv_unsigned sp + -48)%Z |- _ => carve_frame 16%nat S end.
    steps_to 0x108514%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -48)%Z end.
    do 6 hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evtF_done. unfold flush_err_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    split; [eapply ICPT_frame; [exact IC | exact MU | exact WM | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; cbn [fst snd]; lia | apply Forall_nil]]]|].
    exists eflags2, emode2, ee2, ewend2, etail2. unfold file_cells. exact EFC2.
  Qed.
End CharErr.
End CANSEC1.
