(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure Startup_kit Amo_tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit UImg PExitU_tac PIosX_iface PIosX_wide.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac steps_to p := xsteps_to p.

Section WideOut.
  Hypothesis WCR : wcrtomb0_stmt.
  Hypothesis FW0 : fwrite0_out_stmt.
  Hypothesis FFLS : fflush_out_stmt (St := stdout_st) (fun so => so) (fun so _ => so).

  (* [comment removed for export] *)
  Lemma fflush_out_silent :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk usegs m lo (bv_unsigned sp) -> stdout_file m so_x -> so_buf so_x = [] ->
      ssp_cells m guard -> mem_inv usegs m ->
      a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo -> 
      bv_unsigned sp < 2^47 ->
      evt usegs (icpt_post [(bv_unsigned sp - 512, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stdout_file m' (so_inact so_x)))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 PFFLUSH) fc None m (seg_rom usegs)).
  Proof.
    intros until so_x. intros ST SOF EB SSP MI E0 ETP LO GLO SP47.
    pose proof (FFLS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo guard so_x so_x
                  ST SOF eq_refl (fun _ => eq_refl) eq_refl eq_refl SSP MI E0 ETP LO GLO SP47) as H.
    unfold implM, stdout_exit_flush, rd_so, mbind, mget, mret in H. cbn in H. rewrite EB in H. cbn in H.
    eapply evt_mono; [exact H|]. cbv beta. intros ms' (so' & E' & _ & PO). cbn in E'. subst so'. exact PO.
  Qed.

  (* [comment removed for export] *)
  Lemma sync_w_out_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk usegs m lo (bv_unsigned sp) -> stdout_file m so_x -> so_buf so_x = [] ->
      ssp_cells m guard -> ios_wide_shared m -> ios_wcout m -> mem_inv usegs m ->
      a0 = Z_to_bv 64 0xec6f8 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4240 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
      evt usegs (icpt_post [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0xee528, 0xee530)]
                                ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m
                                (fun m' => stdout_file m' (so_inact so_x) /\ rw_cells usegs m' 0xee528 [C8 (Z_to_bv 64 0x10e820)]))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x80e04) fc None m (seg_rom usegs)).
  Proof.
    intros until so_x. intros ST SOF EB SSP IOSW IOSC MI -> -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4240, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0xee528, 0xee530)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    carve_frame 80%nat ST.
    steps_to 0xa86f0%Z.
    apply (rw_cells_split_CB usegs _ _ [] 24 _ _ [8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
    match type of FR with rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?rest) =>
      pose proof (proj1 (rw_cells_app usegs mm A [c1] (c2 :: rest)) FR) as [FRa FRbc];
      pose proof (proj1 (rw_cells_app usegs mm _ [c2] rest) FRbc) as [FRb FRc]; clear FR FRbc end.
    cbn [cells_size csize Nat.add] in FRb, FRc. change (Z.of_nat 8) with 8 in FRb, FRc.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in FRb, FRc by (clear; lia).
    replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) in FRc by (clear; lia).
    call_sp (unshift_w_spec WCR (bv_unsigned sp + -72));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
      ].
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    match goal with
    | TNP : rw_cells usegs ?mm (bv_unsigned sp + -72) [?c2], FRa' : rw_cells usegs ?mm (bv_unsigned sp + -80) [?c1],
      FRc' : rw_cells usegs ?mm (bv_unsigned sp + -64) ?rest |- _ =>
        assert (FR : rw_cells usegs mm (bv_unsigned sp + -80) ([c1] ++ [c2] ++ rest))
          by (apply (proj2 (rw_cells_app usegs mm _ _ _)); split; [exact FRa'|];
              apply (proj2 (rw_cells_app usegs mm _ _ _)); cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8;
              replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by (clear; lia);
              replace (bv_unsigned sp + -72 + 8) with (bv_unsigned sp + -64) by (clear; lia); split; [exact TNP| exact FRc']);
        clear TNP FRa' FRc'; cbn [app] in FR
    end.
    rename POST into CURL1.
    steps_to 0xc3bc8%Z.
    replace (bv_unsigned sp + -64 - (bv_unsigned sp + -64)) with 0 by (clear; lia).
    call_sp (FW0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ so_x);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
 ].
    { exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
    steps_to 0xc2d20%Z.
    call_sp (fflush_out_silent _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (so_act so_x));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
 ].
    hstep. hstep. do 9 hstep.
    change (Z.b2z (0 <? 1) + -1) with 0.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -80)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evt_done. unfold icpt_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [| hyp_by_addr].
    match goal with H : stdout_file _ (so_inact (so_act so_x)) |- _ => exact H end.
  Qed.

  (* [comment removed for export] *)
  Definition flush_w_out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (so_x : stdout_st) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xec928) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0xee528, 0xee530)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ stdout_file m' (so_inact so_x)
      /\ rw_cells usegs m' 0xee528 [C8 (Z_to_bv 64 0x10e820)].

  Lemma flush_w_out_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (so_x : stdout_st),
      stk usegs m lo (bv_unsigned sp) -> stdout_file m so_x -> so_buf so_x = [] ->
      ssp_cells m guard -> ios_wide_shared m -> ios_wcout m -> mem_inv usegs m ->
      a0 = Z_to_bv 64 0xec928 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4288 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
      evt usegs (flush_w_out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard so_x m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x7f754) fc None m (seg_rom usegs)).
  Proof.
    intros until so_x. intros ST SOF EB SSP IOSW IOSC MI -> -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4288, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (0xee528, 0xee530)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    carve_frame 48%nat ST.
    steps_to 0x80e04%Z.
    call_sp (sync_w_out_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ so_x);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
      ].
    { exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_wide_shared. conj_by_addr. }
    { unfold ios_wcout. conj_by_addr. }
    rename POST into CURL2.
    match goal with H : stdout_file _ (so_inact so_x) |- _ => rename H into SOF2 end.
    destruct SOF2 as (flags2 & mode2 & tail2 & bufbytes2 & FC2 & FL722 & BUF2 & BUFP2 & BUFL2 & INACT2).
    unfold file_cells in FC2. cbn [so_inact so_active so_buf so_first so_lbf_nl] in FC2, BUFP2, BUFL2, INACT2. try clear BUF.
    steps_to 0x7f928%Z.
    match goal with S : stk _ _ lo (bv_unsigned sp + -48)%Z |- _ => carve_frame 16%nat S end.
    steps_to 0x7f7d4%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -48)%Z end.
    do 6 hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    apply evt_done. unfold flush_w_out_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    split; [| exact CURL2].
    exists flags2, mode2, tail2, bufbytes2. cbn [so_inact so_active so_buf so_first so_lbf_nl].
    split; [unfold file_cells; exact FC2|]. split; [exact FL722|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact BUFL2| exact INACT2].
  Qed.
End WideOut.
