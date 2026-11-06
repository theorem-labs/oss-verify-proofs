(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit BImg MonadF AExit AIos_tac AIos_iface AIos_dtor AIos_frame AExitU_fini AExitU_tail.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA StepF.
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
Section Head4.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Variables MDPRE ICPT : mem -> Prop.
  Variable ICPTR : footprint -> Prop.
  Variables SLO SHI : Z.
  Hypothesis MDTOR : module_dtor_stmt MDPRE.
  Hypothesis MDPRE_frame : forall W m m', MDPRE m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> MDPRE m'.
  Hypothesis ICPT_frame : forall W m m', ICPT m -> munch W m m' -> wmono bsegs m m' -> Forall exit_wr_ok W -> ICPT m'.
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis WCR : wcrtomb0_stmt ICPT ICPTR SLO SHI.
  Hypothesis FW0 : fwrite0_out_stmt ICPT ICPTR.
  Hypothesis FW0E : fwrite0_err_stmt ICPT ICPTR.
  Hypothesis FFL : fflush_out_stmt ICPT ICPTR get_so set_so.
  Hypothesis FFLS : fflush_out_stmt ICPT ICPTR (St := stdout_st) (fun so => so) (fun so _ => so).
  Hypothesis FFLE : fflush_err_stmt ICPT ICPTR.

  Lemma exit_head4_spec : forall RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word) (so_x : stdout_st),
    MDPRE m -> ICPT m -> ios_cells m ->
    stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m 0x6afa60 [C4 (Z_to_bv 64 t)] ->
    rw_cells bsegs m 0x6cfd78 [C4 z64] ->
    rw_cells bsegs m 0x6cfd98 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells bsegs m 0x6cfb58 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0x6cfb5c [C4 z64] ->
    rw_cells bsegs m 0x6cfb60 [C4 (Z_to_bv 64 4)] ->
    rw_cells bsegs m 0x6cfb68 [C8 (Z_to_bv 64 0x6cfb70)] ->
    rw_cells bsegs m 0x6cfb70 [C8 z64] ->
    rw_cells bsegs m 0x6cfb78 [C8 (Z_to_bv 64 0x152d10); C8 (Z_to_bv 64 0x114748); C8 (Z_to_bv 64 0x757fc)] ->
    rw_cells bsegs m 0x6cfc78 [C8 (Z_to_bv 64 0x9f2c4); C8 (Z_to_bv 64 0x6adba8); C8 z64] ->
    rw_cells bsegs m 0x6cfb90 [C8 (Z_to_bv 64 0x152d10)] ->
    rw_cells bsegs m 0x6cfc90 [C8 (Z_to_bv 64 0xafc8c)] ->
    rw_cells bsegs m 0x6ad6d4 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0x171ff0 [C8 (Z_to_bv 64 0x178878)] ->
    rw_cells bsegs m 0x178894 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0x20cf20 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0x172e08 [C8 (Z_to_bv 64 0x16bf28); C8 (Z_to_bv 64 0x16bf18)] ->
    rw_cells bsegs m 0x16bf18 [C8 (Z_to_bv 64 0xb38c8); C8 (Z_to_bv 64 0x59000)] ->
    rw_cells bsegs m 0x177a10 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0x171fc8 [C8 (Z_to_bv 64 0x152b80); C8 z64] ->
    rw_cells bsegs m 0x173e60 [C8 dso] ->
    rw_cells bsegs m 0x6d0310 [C8 z64] -> rw_cells bsegs m 0x176de8 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells bsegs m RSTDIN stdin_cells ->
    rw_cells bsegs m 0x176ed8 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells bsegs m 0x176cf8 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m so_x -> so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) -> so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->
    stderr_file m ->
    rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->
    mem_inv bsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    0 < t < 4194304 -> lo <= bv_unsigned sp - EXIT_TAIL_DEPTH -> GLOBALS_TOP <= lo -> ATOP <= lo -> SLO <= lo -> bv_unsigned sp <= SHI -> KHIGH <= lo -> bv_unsigned sp mod 16 = 0 ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> ICPTR RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    bv_unsigned sp < 2^47 ->
    implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x152d64) fc None m (seg_rom bsegs)).
  Proof.
    intros until so_x. intros HMD IC IOS ST TID EXL LIBC FIN ALK SLOT HEAD NEXT FF AA F3 A3 INCB GFL FLG COV GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF EB EQ SF SL SEF GG GU MI -> -> Ht LO GLO ATL SLOK SHIK KH AL RSTK RIMG RI RW RG0 SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'. pose proof KH as KH'. unfold KHIGH in KH'. pose proof LO as LO'. unfold EXIT_TAIL_DEPTH in LO'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6cfb58, 0x6cfd80)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    apply implAM_from_evt.
    carve_frame 16%nat ST.
    do 6 hstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    hstep. hstep.
    sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    nstep. sort_lits. amo_step. nstep.
    hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. nstep.
    hstep. hstep.
    carve_frame 48%nat ST.
    steps_to 0x16504c%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    nstep. nstep. hstep.
    replace (sx32 (Z_to_bv 64 4)) with (Z_to_bv 64 4 : word) by (vm_compute; reflexivity).
    steps_to 0xafc8c%Z.
    hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false. hstep.
    steps_to 0x16504c%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep.
    replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3 : word) by (vm_compute; reflexivity).
    steps_to 0x152b14%Z.
    assert (WOK : Forall exit_wr_ok [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6cfb58, 0x6cfd80)]%Z)
      by (unfold exit_wr_ok; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; right; right; left; cbn [fst snd]; lia | apply Forall_nil]]).
    apply evtF_done.
    eapply (exit_tail3_spec get_so set_so MDPRE ICPT ICPTR SLO SHI MDTOR MDPRE_frame ICPT_frame SE WCR FW0 FW0E FFL FFLS FFLE RNG s Q) with (lo := lo) (so_x := so_x) (guard := guard) (t := t);
      try first [ exact EB | exact EQ | exact SF | exact SL | exact LO | exact GLO | exact ATL | exact KH | exact AL | exact RSTK | exact RIMG | exact RW | exact RG0 | exact SP47 | exact RI | exact SLOK | exact SHIK
                | reflexivity
                | (eapply MDPRE_frame; [exact HMD | exact MU | exact WM | exact WOK])
                | (eapply ICPT_frame; [exact IC | exact MU | exact WM | exact WOK])
                | (eapply ios_cells_frame; [exact IOS | exact MU | exact WM | unfold ios_wr_ok; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]]])
                | (exists flags, mode, tail, bufbytes; split; [unfold file_cells; exact FC|]; split; [exact FL72|]; split; [exact BUF|]; split; [exact BUFP|]; split; [exact BUFL| exact INACT])
                | (exists eflags, emode, ee, ewend, etail; unfold file_cells; exact EFC)
                | (unfold got_ssp, ssp_guard, RSTDIN, stdin_cells; hyp_by_addr) ].
  Qed.
End Head4.
End CANSEC1.
