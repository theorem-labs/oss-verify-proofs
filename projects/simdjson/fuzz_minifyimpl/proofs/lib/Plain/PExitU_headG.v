(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure STRW_tac Startup_kit Amo_tac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import F_syscalls StdioFiles Stdio_kit PImg PExitU_tac PExitU_defs PIosX_iface PExitU_tail.
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

Section HeadG.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis WCR : wcrtomb0_stmt.
  Hypothesis FW0 : fwrite0_out_stmt.
  Hypothesis FW0E : fwrite0_err_stmt.
  Hypothesis FFL : fflush_out_stmt get_so set_so.
  Hypothesis FFLS : fflush_out_stmt (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt.

  Lemma exit_headG_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code t : Z) (td0 td1 td2 td3 dso guard : word) (so_x : stdout_st),
    ios_cells m ->
    stk psegs m lo (bv_unsigned sp) ->
    rw_cells psegs m 0xe3960 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)] ->                         (* [comment removed for export] *)
    rw_cells psegs m 0x103c90 [C4 z64] ->                                                                      (* [comment removed for export] *)
    rw_cells psegs m 0x103cbb [C1 (Z_to_bv 8 0)] ->                                                            (* [comment removed for export] *)
    rw_cells psegs m 0x103a70 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2)] ->   (* [comment removed for export] *)
    rw_cells psegs m 0x103a80 [C8 (Z_to_bv 64 0x103a88); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x758f0); C8 (Z_to_bv 64 0xb35fc)] ->  (* [comment removed for export] *)
    rw_cells psegs m 0x103b90 [C8 (Z_to_bv 64 0xe1ac8); C8 (Z_to_bv 64 0x3bc9c)] ->                                                 (* [comment removed for export] *)
    rw_cells psegs m 0xe1784 [C1 (Z_to_bv 8 0)] ->                                                                                (* [comment removed for export] *)
    rw_cells psegs m 0xd0340 [C8 (Z_to_bv 64 0xca418); C8 (Z_to_bv 64 0xca410)] ->
    rw_cells psegs m 0xca410 [C8 (Z_to_bv 64 0x3b7e4)] ->
    rw_cells psegs m 0xd1778 [C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m 0xd0198 [C8 (Z_to_bv 64 0xb346c); C8 z64] ->
    rw_cells psegs m 0xd1368 [C8 dso] ->
    rw_cells psegs m 0x1041f8 [C8 z64] -> rw_cells psegs m 0xd1610 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells psegs m RSTDIN stdin_cells ->
    rw_cells psegs m 0xd1700 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells psegs m 0xd1520 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m so_x -> so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) -> so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->
    stderr_file m ->
    rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells psegs m ssp_guard [C8 guard] ->
    mem_inv psegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    0 < t < 4194304 -> lo <= bv_unsigned sp - EXIT_TAIL_DEPTH -> GLOBALS_TOP <= lo ->
    bv_unsigned sp < 2^47 ->
    implM psegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xb3650) fc None m (seg_rom psegs)).
  Proof.
    intros until so_x. intros IOS ST TID EXL LIBC AT0 AT1 AT2 INCB GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF EB EQ SF SL SEF GG GU MI -> -> Ht LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'. pose proof LO as LO'. unfold EXIT_TAIL_DEPTH in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x103a70, 0x103c98)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    apply implM_from_evt.
    carve_frame 16%nat ST.
    do 6 hstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    hstep. hstep.
    (* [comment removed for export] *)
    sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    nstep. sort_lits. amo_step. nstep.
    hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. nstep.
    hstep. hstep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    steps_to 0xc5028%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    nstep. nstep. hstep.
    replace (sx32 (Z_to_bv 64 2)) with (Z_to_bv 64 2 : word) by (vm_compute; reflexivity).
    (* [comment removed for export] *)
    steps_to 0x3bc9c%Z.
    hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false. hstep.
    (* [comment removed for export] *)
    steps_to 0xc5028%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep.
    replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
    steps_to 0xb3400%Z.
    apply evt_done.
    eapply (exit_tail_spec get_so set_so SE WCR FW0 FW0E FFL FFLS FFLE s Q) with (lo := lo) (so_x := so_x) (guard := guard);
      try first [ exact EB | exact EQ | exact SF | exact SL | exact LO | exact GLO | exact SP47
                | reflexivity
                | (eapply ios_cells_munch; [exact IOS | exact MU | exact WM | unfold ios_addr; cbn [outside]; intros a Ha; lia])
                | (exists flags, mode, tail, bufbytes; split; [unfold file_cells; exact FC|]; split; [exact FL72|]; split; [exact BUF|]; split; [exact BUFP|]; split; [exact BUFL| exact INACT])
                | (exists eflags, emode, ee, ewend, etail; unfold file_cells; exact EFC)
                | (unfold got_ssp, ssp_guard, RSTDIN, stdin_cells; hyp_by_addr) ].
  Qed.
End HeadG.
