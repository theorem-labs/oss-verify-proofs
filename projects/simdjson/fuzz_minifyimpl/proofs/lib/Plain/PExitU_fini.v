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
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import F_syscalls StdioFiles Stdio_kit PImg PExitU_tac PExitU_defs.
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
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma p_Exit_specM : forall {St : Type} (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  mem_inv psegs m ->
  a0 = Z_to_bv 64 code ->
  implM psegs (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xb3358) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros MI ->.
  pose proof (wmono_refl psegs m) as WM.
  apply implM_sys. do 2 lstep. step_ecall.
  split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
Qed.

Section Fini.
  Context {St : Type}.
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).

  (* [comment removed for export] *)
  Lemma stdio_exit_silent :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (so_i : stdout_st) (guard : word),
      stk psegs m lo (bv_unsigned sp) ->
      rw_cells psegs m 0x103cbb [C1 (Z_to_bv 8 0)] ->
      rw_cells psegs m 0x1041f8 [C8 z64] -> rw_cells psegs m 0xd1610 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells psegs m RSTDIN stdin_cells ->
      rw_cells psegs m 0xd1700 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells psegs m 0xd1520 [C8 (Z_to_bv 64 RSTDERR)] ->
      stdout_file m so_i -> so_buf so_i = [] -> stderr_file m ->
      rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells psegs m ssp_guard [C8 guard] ->
      mem_inv psegs m -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 160 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
      evt psegs (fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom psegs)
          /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0xd1700); (RSTDOUT_BUF, 0x104a18)]%Z m m'
          /\ wmono psegs m m' /\ mem_inv psegs m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xb8d70) fc None m (seg_rom psegs)).
  Proof.
    intros until guard. intros ST LIBC OFL SIN SINF SOU SEU SOF EB SEF GG GU MI ETP LO GLO SP47.
    pose proof (SE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo so_i guard
                  ST LIBC OFL SIN SINF SOU SEU SOF SEF GG GU MI ETP LO GLO SP47) as H.
    unfold implM, stdout_exit_flush, rd_so, mbind, mget, mret in H. cbn in H. rewrite EB in H. cbn in H.
    eapply evt_mono; [exact H|]. cbv beta. intros ms' PO. unfold stdio_exit_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & so' & m' & E & MU & WM & MI' & _).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM| exact MI'].
  Qed.

  Lemma exit_fini_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code : Z) (dso guard x1 x2 x3 xs0 xra f0 f1 : word) (j8 : list byte)
      (so_i : stdout_st),
    stk psegs m lo (bv_unsigned sp + -64) ->
    rw_cells psegs m (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0xb36b4)] ->
    rw_cells psegs m (bv_unsigned sp + -16) [C8 xs0; C8 xra] ->
    rw_cells psegs m 0x103cbb [C1 (Z_to_bv 8 0)] ->                                                            (* [comment removed for export] *)
    rw_cells psegs m 0x103a70 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->   (* [comment removed for export] *)
    rw_cells psegs m 0x103a80 [C8 (Z_to_bv 64 0x103a88); C8 (Z_to_bv 64 0); C8 f0; C8 f1] ->                   (* [comment removed for export] *)
    rw_cells psegs m 0xd0340 [C8 (Z_to_bv 64 0xca418); C8 (Z_to_bv 64 0xca410)] ->                           (* [comment removed for export] *)
    rw_cells psegs m 0xca410 [C8 (Z_to_bv 64 0x3b7e4)] ->                                                    (* [comment removed for export] *)
    rw_cells psegs m 0xd1778 [C1 (Z_to_bv 8 0)] ->                                                           (* [comment removed for export] *)
    rw_cells psegs m 0xd0198 [C8 (Z_to_bv 64 0xb346c); C8 z64] ->                                            (* [comment removed for export] *)
    rw_cells psegs m 0xd1368 [C8 dso] ->                                                                     (* [comment removed for export] *)
    rw_cells psegs m 0x1041f8 [C8 z64] -> rw_cells psegs m 0xd1610 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells psegs m RSTDIN stdin_cells ->
    rw_cells psegs m 0xd1700 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells psegs m 0xd1520 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m so_i -> so_buf so_i = [] -> stderr_file m ->
    rw_cells psegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells psegs m ssp_guard [C8 guard] ->
    mem_inv psegs m ->
    tp = Z_to_bv 64 RTP -> s0 = Z_to_bv 64 0x103a74 -> s2 = Z_to_bv 64 0x103a70 ->
    lo <= bv_unsigned sp - 8192 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
    implM psegs (msys (NExit code) dec_exit) s Q
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xb3424) fc None m (seg_rom psegs)).
  Proof.
    intros until so_i. intros ST FRF FRE LIBC AT0 AT1 GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF EB SEF GG GU MI -> -> -> LO GLO SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x103a70, 0x103a88); (0xd1778, 0xd1779)]%Z m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    apply implM_from_evt.
    (* [comment removed for export] *)
    steps_to 0xc5028%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    steps_to 0xc52b0%Z.
    release_frame FRF ST (bv_unsigned sp + -16)%Z.
    steps_to 0xb36b4%Z.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x3b7e4%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. nstep.
    steps_to 0xb346c%Z. hstep.
    steps_to 0x3b870%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end. hstep.
    (* [comment removed for export] *)
    steps_to 0xb36b8%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
    hstep.
    (* [comment removed for export] *)
    clear MU WM.
    call_sp stdio_exit_silent;
      try first [ eassumption | reflexivity | lia | unfold GLOBALS_TOP; lia | hyp_by_addr ].
    { exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    (* [comment removed for export] *)
    hstep. hstep. apply evt_done.
    apply p_Exit_specM; [eassumption | reflexivity].
  Qed.
End Fini.
