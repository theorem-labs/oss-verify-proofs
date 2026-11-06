(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure STRW_tac Startup_kit Amo_tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit UImg PExitU_tac PExitU_defs PIosX_iface PIosX_dtor PExitU_fini.
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

Section Tail.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis WCR : wcrtomb0_stmt.
  Hypothesis FW0 : fwrite0_out_stmt.
  Hypothesis FW0E : fwrite0_err_stmt.
  Hypothesis FFL : fflush_out_stmt get_so set_so.
  Hypothesis FFLS : fflush_out_stmt (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt.

  (* [comment removed for export] *)
  Definition tail_mid (sp gp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo code : Z) (s : St)
      : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (so' : stdout_st) (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word) (m' : mem)
                            (dso guard x1 x2 x3 xs0 xra f0 f1 : word) (j8 : list byte),
      st' = set_so so' s /\ so_buf so' = []
      /\ ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 0x10e5a4) s1 a0 a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0x10e5a0) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0xbdc58) fc None m' (seg_rom usegs)
      /\ stk usegs m' lo (bv_unsigned sp + -64)
      /\ rw_cells usegs m' (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0xbdee8)]
      /\ rw_cells usegs m' (bv_unsigned sp + -16) [C8 xs0; C8 xra]
      /\ rw_cells usegs m' 0x10e7eb [C1 (Z_to_bv 8 0)]
      /\ rw_cells usegs m' 0x10e5a0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
      /\ rw_cells usegs m' 0x10e5b0 [C8 (Z_to_bv 64 0x10e5b8); C8 (Z_to_bv 64 0); C8 f0; C8 f1]
      /\ rw_cells usegs m' 0xdab70 [C8 (Z_to_bv 64 0xd4c48); C8 (Z_to_bv 64 0xd4c40)]
      /\ rw_cells usegs m' 0xd4c40 [C8 (Z_to_bv 64 0x3b8e4)]
      /\ rw_cells usegs m' 0xdc2a8 [C1 (Z_to_bv 8 0)]
      /\ rw_cells usegs m' 0xda9c8 [C8 (Z_to_bv 64 0xbdca0); C8 z64]
      /\ rw_cells usegs m' 0xdbb98 [C8 dso]
      /\ rw_cells usegs m' 0x10ed28 [C8 z64] /\ rw_cells usegs m' 0xdc140 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells usegs m' RSTDIN stdin_cells
      /\ rw_cells usegs m' 0xdc230 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells usegs m' 0xdc050 [C8 (Z_to_bv 64 RSTDERR)]
      /\ stdout_file m' (so_inact so') /\ stderr_file m'
      /\ rw_cells usegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m' ssp_guard [C8 guard]
      /\ mem_inv usegs m'.

  (* [comment removed for export] *)
  Definition EXIT_TAIL_DEPTH : Z := 8192.

  Lemma exit_tail_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code : Z) (dso guard x1 x2 x3 xs0 xra f1 a1' : word) (j8 : list byte)
      (so_x : stdout_st),
    ios_cells m ->
    stk usegs m lo (bv_unsigned sp + -64) ->
    rw_cells usegs m (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0xbdee8)] ->
    rw_cells usegs m (bv_unsigned sp + -16) [C8 xs0; C8 xra] ->
    rw_cells usegs m 0x10e7eb [C1 (Z_to_bv 8 0)] ->                                                            (* [comment removed for export] *)
    rw_cells usegs m 0x10e5a0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->   (* [comment removed for export] *)
    rw_cells usegs m 0x10e5b0 [C8 (Z_to_bv 64 0x10e5b8); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x80124); C8 f1] ->  (* [comment removed for export] *)
    rw_cells usegs m 0x10e6c0 [C8 (Z_to_bv 64 0xec5f8); C8 a1'] ->                                             (* [comment removed for export] *)
    rw_cells usegs m 0xdab70 [C8 (Z_to_bv 64 0xd4c48); C8 (Z_to_bv 64 0xd4c40)] ->
    rw_cells usegs m 0xd4c40 [C8 (Z_to_bv 64 0x3b8e4)] ->
    rw_cells usegs m 0xdc2a8 [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs m 0xda9c8 [C8 (Z_to_bv 64 0xbdca0); C8 z64] ->
    rw_cells usegs m 0xdbb98 [C8 dso] ->
    rw_cells usegs m 0x10ed28 [C8 z64] -> rw_cells usegs m 0xdc140 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells usegs m RSTDIN stdin_cells ->
    rw_cells usegs m 0xdc230 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells usegs m 0xdc050 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m so_x -> so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) -> so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->
    stderr_file m ->
    rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells usegs m ssp_guard [C8 guard] ->
    mem_inv usegs m ->
    tp = Z_to_bv 64 RTP -> s0 = Z_to_bv 64 0x10e5a4 -> s2 = Z_to_bv 64 0x10e5a0 -> a2 = Z_to_bv 64 0 ->
    lo <= bv_unsigned sp - EXIT_TAIL_DEPTH -> GLOBALS_TOP <= lo ->
    bv_unsigned sp < 2^47 ->
    implM usegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbdc34) fc None m (seg_rom usegs)).
  Proof.
    intros until so_x. intros IOS ST FRF FRE LIBC AT0 AT1 AT2 GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF EB EQ SF SL SEF GG GU MI -> -> -> -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'. unfold EXIT_TAIL_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    unfold Driver.exit_model.
    change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (RSTDERR, RSTDERR + 232); (RSTDOUT, RSTDOUT + 232); (0xee528, 0xee530)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    eapply (implM_bind usegs _ _ s (tail_mid sp gp s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code s)).
    - apply implM_from_evt.
      (* [comment removed for export] *)
      steps_to 0xcfae4%Z.
      hstep. nstep. hstep.
      steps_to 0x80124%Z.
      assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - RSP LO GLO'; lia).
      apply evt_done.
      eapply implM_post_evt'.
      { eapply (ios_dtor_spec get_so set_so WCR FW0 FW0E FFL FFLS FFLE) with (lo := lo) (guard := guard) (so_x := so_x);
          [ rewrite ESP; exact ST
          | exists flags, mode, tail, bufbytes; split; [unfold file_cells; exact FC|]; split; [exact FL72|]; split; [exact BUF|]; split; [exact BUFP|]; split; [exact BUFL| exact INACT]
          | exists eflags, emode, ee, ewend, etail; unfold file_cells; exact EFC
          | exact EB | exact EQ | exact SF | exact SL
          | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GG| exact GU]
          | exact IOS
          | exact MI | reflexivity
          | rewrite ESP; clear - LO; lia | exact GLO | rewrite ESP; clear - SP47; lia ]. }
      cbv beta. intros [] st2 ms2 (so' & -> & EB' & PO2).
      destruct PO2 as (t0' & t1' & t2' & a0' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & SSP2 & SOF2 & SEF2 & CURL2).
      rewrite ESP in MU2, ST2.
      rewrite (ret_pc_even 777304) by (cbn; lia).
      transport_after_call usegs m m2 MU2 WM2.   (* [comment removed for export] *)
      destruct SSP2 as [GG2 GU2]. unfold got_ssp, ssp_guard in GG2, GU2.
      apply evt_done. unfold tail_mid.
      exists so'. do 18 eexists. exists m2. exists dso, guard. do 7 eexists. eexists.
      split; [reflexivity|]. split; [exact EB'|]. split; [reflexivity|].
      split; [exact ST2|].
      unfold RSTDIN, stdin_cells, got_ssp, ssp_guard.
      repeat (lazymatch goal with |- rw_cells _ _ _ _ /\ _ => split; [hyp_by_addr|] end).
      split; [exact SOF2|]. split; [exact SEF2|].
      repeat (lazymatch goal with |- rw_cells _ _ _ _ /\ _ => split; [hyp_by_addr|] end).
      exact MI2.
    - intros [] st' ms' TM. unfold tail_mid in TM.
      destruct TM as (so' & ra' & t0' & t1' & t2' & s1' & a0' & a1'' & a2'' & a3' & a4' & a5' & a6' & a7' & s3' & t3' & t4' & t5' & t6' & m' &
                      dso' & guard' & x1' & x2' & x3' & xs0' & xra' & f0' & f1' & j8' &
                      -> & EB' & -> & TM).
      destruct TM as (ST' & FRF' & FRE' & LIBC' & AT0' & AT1' & GF' & FA' & FINZ' & GCX' & DSO' &
                      OFL' & SIN' & SINF' & SOU' & SEU' & SOF' & SEF' & GG' & GU' & MI').
      eapply (exit_fini_spec SE) with (so_i := so_inact so') (lo := lo);
        try first [ eassumption | reflexivity | exact LO | exact GLO | exact SP47 ].
  Qed.
End Tail.
