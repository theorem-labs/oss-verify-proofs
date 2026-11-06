(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit BImg MonadF AIos_tac AIos_iface AIos_wide.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ITreeA StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import F_fmt_fp_lib RunDraw.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section WideOut.
  Variable ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Variables SLO SHI : Z.
  Hypothesis WCR : wcrtomb0_stmt ICPT ICPTR SLO SHI.
  Hypothesis FW0 : fwrite0_out_stmt ICPT ICPTR.
  Hypothesis FFLS : fflush_out_stmt ICPT ICPTR (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis ICPT_frame : forall W m m', ICPT m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => ATOP <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= RSTDOUT + 232) \/ (0x6afad8 <= fst iv /\ snd iv <= 0x6afae0)) W -> ICPT m'.

  (* [comment removed for export] *)
  Lemma fflush_out_silent :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk bsegs m lo (bv_unsigned sp) -> stdout_file m so_x -> so_buf so_x = [] ->
      ssp_cells m guard -> ICPT m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG -> rng0 RNG -> bv_unsigned sp < 2^47 ->
      evtF bsegs RNG (icpt_post ICPT [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stdout_file m' (so_inact so_x)))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 FFLUSH_STUB) fc None m (seg_rom bsegs)).
  Proof.
    intros until so_x. intros ST SOF EB SSP IC MI E0 ETP LO GLO ATL AL RSTK RIMG RI RG0 SP47.
    pose proof (FFLS RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo guard so_x so_x
                  ST SOF eq_refl (fun _ => eq_refl) eq_refl eq_refl SSP IC MI E0 ETP LO GLO ATL AL RSTK RIMG RI RG0 SP47) as H.
    unfold implAM, stdout_exit_flush, rd_so, mbind, mget, mret in H. cbn in H. rewrite EB in H. cbn in H.
    eapply evtF_mono; [exact H|]. cbv beta. intros ms' [_ (so' & E' & _ & PO)]. cbn in E'. subst so'. exact PO.
  Qed.

  (* [comment removed for export] *)
  Lemma sync_w_out_spec :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk bsegs m lo (bv_unsigned sp) -> stdout_file m so_x -> so_buf so_x = [] ->
      ssp_cells m guard -> ICPT m -> ios_wide_shared m -> ios_wcout m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 0x6adca8 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4240 -> GLOBALS_TOP <= lo -> ATOP <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG -> rng0 RNG ->
      evtF bsegs RNG (icpt_post ICPT [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0x6afad8, 0x6afae0)]
                                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stdout_file m' (so_inact so_x) /\ rw_cells bsegs m' 0x6afad8 [C8 (Z_to_bv 64 0x6cfdd0)]))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x115428) fc None m (seg_rom bsegs)).
  Proof.
    intros until so_x. intros ST SOF EB SSP IC IOSW IOSC MI -> -> LO GLO ATL SLOK SHIK AL SP47 RSTK RIMG RI RG0.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0x6afad8, 0x6afae0)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    carve_frame 80%nat ST.
    steps_to 0x13cdd4%Z.
    apply (rw_cells_split_CB bsegs _ _ [] 24 _ _ [8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    match type of FR with rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?rest) =>
      pose proof (proj1 (rw_cells_app bsegs mm A [c1] (c2 :: rest)) FR) as [FRa FRbc];
      pose proof (proj1 (rw_cells_app bsegs mm _ [c2] rest) FRbc) as [FRb FRc]; clear FR FRbc end.
    cbn [cells_size csize Nat.add] in FRb, FRc. change (Z.of_nat 8) with 8 in FRb, FRc.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FRb, FRc by (clear; lia).
    replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in FRc by (clear; lia).
    call_sp (unshift_w_spec ICPT ICPTR SLO SHI WCR ICPT_frame RNG (bv_unsigned sp + -72));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia)
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM |
                     apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]]]) ].
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    match goal with
    | TNP : rw_cells bsegs ?mm (bv_unsigned sp + -72) [?c2], FRa' : rw_cells bsegs ?mm (bv_unsigned sp + -80) [?c1],
      FRc' : rw_cells bsegs ?mm (bv_unsigned sp + -64) ?rest |- _ =>
        assert (FR : rw_cells bsegs mm (bv_unsigned sp + -80) ([c1] ++ [c2] ++ rest))
          by (apply (proj2 (rw_cells_app bsegs mm _ _ _)); split; [exact FRa'|];
              apply (proj2 (rw_cells_app bsegs mm _ _ _)); cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8;
              replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by (clear; lia);
              replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by (clear; lia); split; [exact TNP| exact FRc']);
        clear TNP FRa' FRc'; cbn [app] in FR
    end.
    rename POST into CURL1.
    steps_to 0x6b0f4%Z.
    replace (bv_unsigned sp + -64 - (bv_unsigned sp + -64)) with 0 by (clear; lia).
    call_sp (FW0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ so_x);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia) ].
    { exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
    steps_to 0x6b154%Z.
    call_sp (fflush_out_silent RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (so_act so_x));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia) ].
    hstep. hstep. do 9 hstep.
    change (Z.b2z (0 <? 1) + -1) with 0.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -80)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evtF_done. unfold icpt_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|]. split; [| hyp_by_addr].
    match goal with H : stdout_file _ (so_inact (so_act so_x)) |- _ => exact H end.
  Qed.

  (* [comment removed for export] *)
  Definition flush_w_out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (so_x : stdout_st) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aded8) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0x6afad8, 0x6afae0)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ ICPT m' /\ stdout_file m' (so_inact so_x)
      /\ rw_cells bsegs m' 0x6afad8 [C8 (Z_to_bv 64 0x6cfdd0)].

  Lemma flush_w_out_spec :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk bsegs m lo (bv_unsigned sp) -> stdout_file m so_x -> so_buf so_x = [] ->
      ssp_cells m guard -> ICPT m -> ios_wide_shared m -> ios_wcout m -> mem_inv bsegs m ->
      a0 = Z_to_bv 64 0x6aded8 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4288 -> GLOBALS_TOP <= lo -> ATOP <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG -> rng0 RNG ->
      evtF bsegs RNG (flush_w_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard so_x m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x113d78) fc None m (seg_rom bsegs)).
  Proof.
    intros until so_x. intros ST SOF EB SSP IC IOSW IOSC MI -> -> LO GLO ATL SLOK SHIK AL SP47 RSTK RIMG RI RG0.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0x6afad8, 0x6afae0)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    carve_frame 48%nat ST.
    steps_to 0x115428%Z.
    call_sp (sync_w_out_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ so_x);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
                | (eapply rng_sub'; [exact RSTK | lia])
                | (clear - AL; Z.div_mod_to_equations; lia)
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM |
                     apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]]]) ].
    { exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    { unfold ios_wcout. conj_by_addr. }
    rename POST into CURL2.
    match goal with H : stdout_file _ (so_inact so_x) |- _ => rename H into SOF2 end.
    destruct SOF2 as (flags2 & mode2 & tail2 & bufbytes2 & FC2 & FL722 & BUF2 & BUFP2 & BUFL2 & INACT2).
    unfold file_cells in FC2. cbn [so_inact so_active so_buf so_first so_lbf_nl] in FC2, BUFP2, BUFL2, INACT2. try clear BUF.
    steps_to 0x113f4c%Z.
    match goal with S : stk _ _ lo (bv_unsigned sp + -48)%Z |- _ => carve_frame 16%nat S end.
    steps_to 0x113df8%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -48)%Z end.
    do 6 hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evtF_done. unfold flush_w_out_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    split; [eapply ICPT_frame; [exact IC | exact MU | exact WM |
              apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; left; cbn [fst snd]; lia | apply Forall_cons; [right; right; cbn [fst snd]; lia | apply Forall_nil]]]]|].
    split; [| exact CURL2].
    exists flags2, mode2, tail2, bufbytes2. cbn [so_inact so_active so_buf so_first so_lbf_nl].
    split; [unfold file_cells; exact FC2|]. split; [exact FL722|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact BUFL2| exact INACT2].
  Qed.
End WideOut.
End CANSEC1.
