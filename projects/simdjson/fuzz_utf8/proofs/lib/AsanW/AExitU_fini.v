(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import F_syscalls StdioFiles Stdio_kit AImg MonadF AExit AIos_tac.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Export AExitU_wr.
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
Section Fini.
  Context {St : Type}.
  Variable MDPRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt MDPRE.
  Hypothesis MDPRE_frame : forall W m m', MDPRE m -> munch W m m' -> wmono asegs m m' -> Forall exit_wr_ok W -> MDPRE m'.
  Hypothesis SE : stdio_exit_spec_stmt2 (St := stdout_st) (fun so => so) (fun so _ => so).

  (* [comment removed for export] *)
  Lemma stdio_exit_silent :
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (so_i : stdout_st) (guard : word) (cdt thr sec : byte) (tm1 : word),
      stk asegs m lo (bv_unsigned sp) ->
      rw_cells asegs m 0x6c3a18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      rw_cells asegs m 0x6c3f90 [C8 z64] -> rw_cells asegs m 0x16aac0 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells asegs m RSTDIN stdin_cells ->
      rw_cells asegs m 0x16abb0 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0x16a9d0 [C8 (Z_to_bv 64 RSTDERR)] ->
      stdout_file m so_i -> so_buf so_i = [] -> stderr_file m ->
      rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
      mem_inv asegs m -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 160 -> GLOBALS_TOP <= lo ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG -> bv_unsigned sp < 2^47 ->
      evtF asegs RNG (fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom asegs)
          /\ munch [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x16abb0); (RSTDOUT_BUF, 0x6c47b0)]%Z m m'
          /\ wmono asegs m m' /\ mem_inv asegs m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14ed64) fc None m (seg_rom asegs)).
  Proof.
    intros until tm1. intros ST LIBC OFL SIN SINF SOU SEU SOF EB SEF GG GU MI ETP LO GLO RSTK RIMG RG0 SP47.
    pose proof (SE RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo so_i guard cdt thr sec tm1
                  ST LIBC OFL SIN SINF SOU SEU SOF SEF GG GU MI ETP LO GLO RSTK RIMG RG0 SP47) as H.
    unfold implAM, stdout_exit_flush, rd_so, mbind, mget, mret in H. cbn in H. rewrite EB in H. cbn in H.
    eapply evtF_mono; [exact H|]. cbv beta. intros ms' [_ PO]. unfold stdio_exit_post in PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & so' & m' & E & MU & WM & MI' & _).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM| exact MI'].
  Qed.

  Lemma exit_fini_spec : forall RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (code : Z) (cdt thr sec : byte) (tm1 dso guard x1 x2 x3 xs0 xra f1 f2 a1' a2' : word) (j8 : list byte)
      (so_i : stdout_st),
    MDPRE m ->
    stk asegs m lo (bv_unsigned sp + -64) ->
    rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 x3; C8 x2; C8 x1; C8 (Z_to_bv 64 code); C8 (Z_to_bv 64 0x146e90)] ->
    rw_cells asegs m (bv_unsigned sp + -16) [C8 xs0; C8 xra] ->
    rw_cells asegs m 0x6c3a18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
    rw_cells asegs m 0x6c37d8 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x6c37dc [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells asegs m 0x6c37e0 [C4 (Z_to_bv 64 1)] ->                                  (* [comment removed for export] *)
    rw_cells asegs m 0x6c37e8 [C8 (Z_to_bv 64 0x6c37f0)] ->                           (* [comment removed for export] *)
    rw_cells asegs m 0x6c37f0 [C8 z64] ->                                             (* [comment removed for export] *)
    rw_cells asegs m 0x6c37f8 [C8 (Z_to_bv 64 0x146dd8); C8 f1; C8 f2] ->
    rw_cells asegs m 0x6c38f8 [C8 (Z_to_bv 64 0x9f478); C8 a1'; C8 a2'] ->
    rw_cells asegs m 0x200ba0 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x166ec8 [C8 (Z_to_bv 64 0x15fff0); C8 (Z_to_bv 64 0x15ffe0)] -> (* [comment removed for export] *)
    rw_cells asegs m 0x15ffe0 [C8 (Z_to_bv 64 0xb32d0); C8 (Z_to_bv 64 0x591b4)] ->  (* [comment removed for export] *)
    rw_cells asegs m 0x16b690 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x166088 [C8 (Z_to_bv 64 0x146c48); C8 z64] ->                   (* [comment removed for export] *)
    rw_cells asegs m 0x167f08 [C8 dso] ->                                             (* [comment removed for export] *)
    rw_cells asegs m 0x6c3f90 [C8 z64] -> rw_cells asegs m 0x16aac0 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells asegs m RSTDIN stdin_cells ->
    rw_cells asegs m 0x16abb0 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0x16a9d0 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m so_i -> so_buf so_i = [] -> stderr_file m ->
    rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTP -> s0 = Z_to_bv 64 0x6c37dc -> s2 = Z_to_bv 64 0x6c37d8 ->
    lo <= bv_unsigned sp - 8192 -> GLOBALS_TOP <= lo -> ATOP <= lo -> KHIGH <= lo -> bv_unsigned sp mod 16 = 0 ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    bv_unsigned sp < 2^47 ->
    implAM RNG (msys (NExit code) dec_exit) s Q
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x146c00) fc None m (seg_rom asegs)).
  Proof.
    intros until so_i. intros HMD ST FRF FRE LIBC FIN ALK SLOT HEAD NEXT FF AA COV GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF EB SEF GG GU MI -> -> -> LO GLO ATL KH AL RSTK RIMG RW RG0 SP47.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'. pose proof KH as KH'. unfold KHIGH in KH'.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT). unfold file_cells in FC.
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC). unfold file_cells in EFC.
    pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6c37d8, 0x6c3a00); (0x16b690, 0x16b691)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    apply implAM_from_evt.
    (* [comment removed for export] *)
    steps_to 0x159114%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    steps_to 0x9f478%Z.
    hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). nstep. hstep.
    (* [comment removed for export] *)
    steps_to 0x159114%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    steps_to 0x15939c%Z.
    release_frame FRF ST (bv_unsigned sp + -16)%Z.
    steps_to 0x146e90%Z.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x591b4%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. nstep.
    steps_to 0x146c48%Z. hstep.
    steps_to 0x59240%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end. hstep.
    (* [comment removed for export] *)
    steps_to 0xb32d0%Z.
    match goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mc _) =>
      assert (HMD1 : MDPRE mc)
        by (eapply MDPRE_frame; [exact HMD | exact MU | exact WM |
              apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; right; right; left; cbn [fst snd]; lia |
              apply Forall_cons; [right; right; right; right; cbn [fst snd]; lia | apply Forall_nil]]]]);
      assert (MU2 : munch [(bv_unsigned sp - 8192, bv_unsigned sp); (0x6c37d8, 0x6c3a00); (0x16b690, 0x16b691);
                           (0x16b640, 0x16b648); (0x16c5b0, 0x16c5b8); (0x6a15e0, 0x6a15ea);
                           (0x7fffc6c0, 0x7fffd70c); (0x8002407c, 0x800240ac); (0x800cc270, 0x800cc2bc); (0x8002557c, 0x800256c4)]%Z m mc)
        by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MU
    end.
    call_sp (MDTOR RNG); try first [ exact HMD1 | eassumption | unfold MDTOR_DEPTH; lia | unfold KHIGH; lia | exact RW ].
    1:{ eapply rng_sub'; [exact RSTK | lia]. }
    (* [comment removed for export] *)
    steps_to 0x146e94%Z.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
    hstep.
    (* [comment removed for export] *)
    clear MU2 WM.
    call_sp (stdio_exit_silent RNG);
      try first [ eassumption | reflexivity | exact RIMG | exact RG0 | lia | unfold GLOBALS_TOP; lia
                | (eapply rng_sub'; [exact RSTK | lia]) | hyp_by_addr ].
    { exists flags, mode, tail, bufbytes. split; [unfold file_cells; exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [exact BUFP|]. split; [exact BUFL| exact INACT]. }
    { exists eflags, emode, ee, ewend, etail. unfold file_cells. exact EFC. }
    (* [comment removed for export] *)
    hstep. hstep. apply evtF_done.
    apply a_Exit_specM; [eassumption | reflexivity].
  Qed.
End Fini.
End CANSEC1.
