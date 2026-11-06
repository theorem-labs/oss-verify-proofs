(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import F_syscalls StdioFiles Stdio_kit PImg PExitU_tac PIosX_iface.
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

Section Char.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis FW0 : fwrite0_out_stmt.
  Hypothesis FFL : fflush_out_stmt get_so set_so.

  Definition SYNC_DEPTH : Z := 80 + PIOSX_DEPTH.

  Lemma sync_out_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St) (so_x : stdout_st),
      stk psegs m lo (bv_unsigned sp) -> stdout_file m so_x ->
      so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) -> so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->
      ssp_cells m guard -> ios_char_shared m -> ios_cout m -> mem_inv psegs m ->
      a0 = Z_to_bv 64 0xe1b08 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - SYNC_DEPTH -> GLOBALS_TOP <= lo ->
      bv_unsigned sp < 2^47 ->
      implM psegs (stdout_exit_flush get_so set_so) s
             (fun _ st' ms' => exists so', st' = set_so so' s /\ so_buf so' = []
                /\ icpt_post [(bv_unsigned sp - SYNC_DEPTH, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]
                             ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m (fun m' => stdout_file m' (so_inact so')) ms')
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x75e6c) fc None m (seg_rom psegs)).
  Proof.
    intros until so_x. intros ST SOF EB EQ SF SL SSP IOSS IOSC MI -> -> LO GLO SP47.
    unfold SYNC_DEPTH, PIOSX_DEPTH, GLOBALS_TOP in *.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold file_cells in FC.
    destruct IOSS as (VB & SYNCV & CVP & UNSH). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - (80 + 512), bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    apply implM_from_evt.
    carve_frame 80%nat ST.
    steps_to 0x9d6f0%Z.
    nstep. nstep. nstep.
    steps_to 0xb9394%Z.
    replace (bv_unsigned sp + -64 - (bv_unsigned sp + -64)) with 0 by (clear; lia).
    call_sp FW0;
      try first [ eassumption | reflexivity | unfold GLOBALS_TOP; lia
                | (split; hyp_by_addr)
                | (exists flags, mode, tail, bufbytes; repeat split; first [hyp_by_addr | assumption]) ].
    { exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
    { unfold ssp_cells, got_ssp, ssp_guard. split; [exact GOT| exact GUARD]. }
    (* [comment removed for export] *)
    steps_to 0xb84ec%Z.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    apply evt_done.
    eapply implM_post_evt'.
    { eapply FFL with (lo := lo) (guard := guard) (so_x := so_act so_x);
        [ rewrite ESP; exact PC | exact POST | exact EB
        | intros NE; rewrite <- (EQ NE); destruct so_x as [act bf lb fi]; cbn [so_act so_buf so_lbf_nl so_first]; cbn [so_buf] in EB;
          destruct act; [reflexivity| exfalso; apply NE; rewrite <- EB; exact (INACT eq_refl)]
        | exact SF | exact SL
        | exact PC0 | exact MI0 | reflexivity | reflexivity
        | rewrite ESP; clear - LO; lia | unfold GLOBALS_TOP; exact GLO | rewrite ESP; clear - SP47; lia ]. }
    cbv beta. intros [] st2 ms2 (so' & -> & EB' & PO2).
    destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & SOF2).
    rewrite ESP in MU2, ST2.
    rewrite (ret_pc_even 483068) by (cbn; lia).
    match goal with WMx : wmono psegs m ?mc |- _ => transport_after_call psegs mc m2 MU2 WM2 end.
    hstep. hstep. do 9 hstep.
    change (Z.b2z (0 <? 1) + -1) with 0.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -80)%Z _ |- _ => release_frame H ST2 (bv_unsigned sp) end.
    apply evt_done. exists so'. split; [reflexivity|]. split; [exact EB'|].
    unfold icpt_post. do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact SSP2| exact SOF2].
  Qed.

  (* [comment removed for export] *)
  Definition FLUSH_DEPTH : Z := 48 + SYNC_DEPTH.

  Lemma flush_out_spec :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St) (so_x : stdout_st),
      stk psegs m lo (bv_unsigned sp) -> stdout_file m so_x ->
      so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) -> so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->
      ssp_cells m guard -> ios_char_shared m -> ios_cout m -> mem_inv psegs m ->
      a0 = Z_to_bv 64 0xe1d58 -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - FLUSH_DEPTH -> GLOBALS_TOP <= lo ->
      bv_unsigned sp < 2^47 ->
      implM psegs (stdout_exit_flush get_so set_so) s
             (fun _ st' ms' => exists so', st' = set_so so' s /\ so_buf so' = []
                /\ exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
                  ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xe1d58) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (ret_pc ra) fc None m' (seg_rom psegs)
                  /\ munch [(bv_unsigned sp - 640, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
                  /\ stk psegs m' lo (bv_unsigned sp) /\ ssp_cells m' guard /\ stdout_file m' (so_inact so'))
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x74804) fc None m (seg_rom psegs)).
  Proof.
    intros until so_x. intros ST SOF EB EQ SF SL SSP IOSS IOSC MI -> -> LO GLO SP47.
    unfold FLUSH_DEPTH, SYNC_DEPTH, PIOSX_DEPTH in LO. pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold file_cells in FC.
    destruct IOSS as (VB & SYNCV & CVP & UNSH). destruct IOSC as (O1 & O2 & O3 & O4 & O5 & B1 & B2).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (munch_refl [(bv_unsigned sp - 640, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    apply implM_from_evt.
    carve_frame 48%nat ST.
    steps_to 0x75e6c%Z.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - RSP LO GLO'; lia).
    apply evt_done.
    eapply implM_post_evt'.
    { eapply sync_out_spec with (lo := lo) (guard := guard) (so_x := so_x);
        [ rewrite ESP; exact ST
        | exists flags, mode, tail, bufbytes; split; [unfold file_cells; exact FC|]; split; [exact FL72|]; split; [exact BUF|]; split; [exact BUFP|]; split; [exact BUFL| exact INACT]
        | exact EB | exact EQ | exact SF | exact SL
        | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]
        | unfold ios_char_shared; conj_by_addr | unfold ios_cout; conj_by_addr
        | exact MI | reflexivity | reflexivity
        | rewrite ESP; unfold SYNC_DEPTH, PIOSX_DEPTH; clear - LO; lia | exact GLO | rewrite ESP; clear - SP47; lia ]. }
    cbv beta. intros [] st2 ms2 (so' & -> & EB' & PO2).
    destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & SOF2).
    rewrite ESP in MU2, ST2. unfold SYNC_DEPTH, PIOSX_DEPTH in MU2.
    destruct SOF2 as (flags2 & mode2 & tail2 & bufbytes2 & FC2 & FL722 & BUF2 & BUFP2 & BUFL2 & INACT2).
    unfold file_cells in FC2. cbn [so_inact so_active so_buf so_first so_lbf_nl] in FC2, BUFP2, BUFL2, INACT2. clear BUF.
    rewrite (ret_pc_even 477276) by (cbn; lia).
    match goal with WMx : wmono psegs m ?mc |- _ => transport_after_call psegs mc m2 MU2 WM2 end.
    (* [comment removed for export] *)
    steps_to 0x749d8%Z.
    carve_frame 16%nat ST2.
    steps_to 0x74884%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _ |- _ => release_frame H ST2 (bv_unsigned sp + -48)%Z end.
    do 6 hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _ |- _ => release_frame H ST2 (bv_unsigned sp) end.
    apply evt_done. exists so'. split; [reflexivity|]. split; [exact EB'|].
    do 14 eexists. eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST2|].
    split; [unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT| exact GUARD]|].
    exists flags2, mode2, tail2, bufbytes2. cbn [so_inact so_active so_buf so_first so_lbf_nl].
    split; [unfold file_cells; exact FC2|]. split; [exact FL722|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact BUFL2| exact INACT2].
  Qed.
End Char.
