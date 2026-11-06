(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure Startup_kit Amo_tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import F_syscalls StdioFiles Stdio_kit PImg PExitU_tac PIosX_iface PIosX_char PIosX_char_err PIosX_wide PIosX_wide_out.
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

Section Dtor.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis WCR : wcrtomb0_stmt.
  Hypothesis FW0 : fwrite0_out_stmt.
  Hypothesis FW0E : fwrite0_err_stmt.
  Hypothesis FFL : fflush_out_stmt get_so set_so.
  Hypothesis FFLS : fflush_out_stmt (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt.

  Definition IOS_DTOR_DEPTH : Z := 4304.

  Definition ios_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (guard : word) (m : mem) (s : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (so' : stdout_st), st' = set_so so' s /\ so_buf so' = []
      /\ exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom psegs)
        /\ munch [(bv_unsigned sp - 4304, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232); (0xe39f8, 0xe3a00)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
        /\ stk psegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ stdout_file m' (so_inact so') /\ stderr_file m'
        /\ rw_cells psegs m' 0xe39f8 [C8 (Z_to_bv 64 0x103cf0)].

  Lemma ios_dtor_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St) (so_x : stdout_st),
      stk psegs m lo (bv_unsigned sp) -> stdout_file m so_x -> stderr_file m ->
      so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) -> so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->
      ssp_cells m guard -> ios_cells m -> mem_inv psegs m ->
      tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 4304 -> GLOBALS_TOP <= lo -> 
      bv_unsigned sp < 2^47 ->
      implM psegs (stdout_exit_flush get_so set_so) s
             (ios_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x758f0) fc None m (seg_rom psegs)).
  Proof.
    intros until so_x. intros ST SOF SEF EB EQ SF SL SSP IOS MI -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD.
    destruct IOS as (IOSS & IOSC & IOSL & IOSW & IOSWC & IOSWL).
    destruct IOSS as (VB & SYNCV & CVP & UNSH). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    destruct IOSL as (L1 & L2 & L3 & L4 & L5 & LB1 & LB2).
    destruct IOSW as (VBW & SYNCW & CVW & UNSW & LOC & CURL). destruct IOSWC as (WO1 & WO2 & WO3 & WO4 & WO5 & WB1 & WB2).
    destruct IOSWL as (WL1 & WL2 & WL3 & WL4 & WL5 & WLB1 & WLB2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 4304, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232); (0xe39f8, 0xe3a00)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    apply implM_from_evt.
    carve_frame 16%nat ST.
    steps_to 0x74804%Z.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - RSP LO GLO'; lia).
    apply evt_done.
    eapply implM_post_evt'.
    { eapply (flush_out_spec get_so set_so FW0 FFL) with (lo := lo) (guard := guard) (so_x := so_x);
        [ rewrite ESP; exact ST
        | exists flags, mode, tail, bufbytes; split; [unfold file_cells; exact FC|]; split; [exact FL72|]; split; [exact BUF|]; split; [exact BUFP|]; split; [exact BUFL| exact INACT]
        | exact EB | exact EQ | exact SF | exact SL
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]
        | unfold ios_char_shared; conj_by_addr | unfold ios_cout; conj_by_addr
        | exact MI | reflexivity | reflexivity
        | rewrite ESP; unfold FLUSH_DEPTH, SYNC_DEPTH, PIOSX_DEPTH; clear - LO; lia | exact GLO | rewrite ESP; clear - SP47; lia ]. }
    cbv beta. intros [] st2 ms2 (so' & -> & EB' & PO2).
    destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & SOF2).
    rewrite ESP in MU2, ST2.
    destruct SOF2 as (flags2 & mode2 & tail2 & bufbytes2 & FC2 & FL722 & BUF2 & BUFP2 & BUFL2 & INACT2).
    unfold file_cells in FC2. cbn [so_inact so_active so_buf so_first so_lbf_nl] in FC2, BUFP2, BUFL2, INACT2. clear BUF.
    rewrite (ret_pc_even 481548) by (cbn; lia).
    match goal with WMx : wmono psegs m ?mc |- _ => transport_after_call psegs mc m2 MU2 WM2 end.
    clear SSP2 MU2 WM2.
    (* [comment removed for export] *)
    steps_to 0x74804%Z.
    call_sp (flush_err_spec FW0E FFLE);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
 ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    { unfold ios_char_shared. conj_by_addr. }
    { unfold ios_clog. conj_by_addr. }
    clear eflags emode ee ewend etail.
    destruct POST as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    (* [comment removed for export] *)
    steps_to 0x74f20%Z.
    call_sp (flush_w_out_spec WCR FW0 FFLS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (so_inact so'));
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
 ].
    { exists flags2, mode2, tail2, bufbytes2. cbn [so_inact so_active so_buf so_first so_lbf_nl].
      split; [unfold file_cells; exact FC2|]. split; [exact FL722|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact BUFL2| exact INACT2]. }
    { unfold ios_wide_shared. conj_by_addr. }
    { unfold ios_wcout. conj_by_addr. }
    rename POST into CURL3.
    match goal with H : stdout_file _ (so_inact (so_inact so')) |- _ => rename H into SOF3 end.
    clear FL722 BUF2 BUFP2 BUFL2 INACT2.
    destruct SOF3 as (flags3 & mode3 & tail3 & bufbytes3 & FC3 & FL723 & BUF3 & BUFP3 & BUFL3 & INACT3).
    unfold file_cells in FC3. cbn [so_inact so_active so_buf so_first so_lbf_nl] in FC3, BUFP3, BUFL3, INACT3.
    (* [comment removed for export] *)
    steps_to 0x74f20%Z.
    call_sp (flush_w_err_spec WCR FW0E FFLE);
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia | lia
 ].
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    { unfold ios_wide_shared. conj_by_addr. }
    { unfold ios_wclog. conj_by_addr. }
    rename POST into CURL4.
    match goal with H : stderr_file _ |- _ => destruct H as (eflags4 & emode4 & ee4 & ewend4 & etail4 & EFC4) end. unfold file_cells in EFC4.
    hstep. hstep. hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -16)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
    hstep.
    apply evt_done. unfold ios_dtor_post. exists so'. split; [reflexivity|]. split; [exact EB'|].
    do 15 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|].
    split; [exists flags3, mode3, tail3, bufbytes3; cbn [so_inact so_active so_buf so_first so_lbf_nl];
            split; [unfold file_cells; exact FC3|]; split; [exact FL723|]; split; [exact BUF3|]; split; [exact BUFP3|]; split; [exact BUFL3| exact INACT3]|].
    split; [exists eflags4, emode4, ee4, ewend4, etail4; unfold file_cells; exact EFC4| exact CURL4].
  Qed.
End Dtor.
