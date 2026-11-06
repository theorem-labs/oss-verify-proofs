(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Ox.S150_001.   (* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require UImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
Module Drv_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_base.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.

  (* [comment removed for export] *)
  Lemma main_epilogue_exit :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (fs : Fs) (FD : list (word * FdEntry)) (lo code : Z) (tid : word) (so : stdout_st)
           (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (cdt thr sec : byte) (tm1 guard : word) (ph : bool),
      DMOD fs FD mo -> (FD = FDS0 \/ exists e, FD = FDS3 e) ->
      s0 = wz code -> 0 <= code < 256 -> tp = wz PTP ->
      rw_cells usegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 (wz PSTAGE2_RET)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 256 -> GLOBALS_TOP <= lo -> bv_unsigned sp + 80 < 2^63 ->
      DSTAT ph tid m -> 0 < bv_unsigned tid < 2^22 ->
      rw_cells usegs m 0x54c58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m -> ssp_cells m guard ->
      mem_inv usegs m ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x13368) fc None m (seg_rom usegs)) mo)
               (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz code) fs)).
  Proof.
    intros until ph. intros DM HFD -> CODE -> FR ST LO GT SPH DS TID LC SOF SOB SEF [SSP1 SSP2] MI.
    pose proof DM as [MOK' _ HFS]. destruct (DMOD_chan _ _ _ DM HFD) as [CH1 CH2].
    destruct DS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16). unfold PDSO, PINCB, PCXAFIN in *.
    pose proof ST as LNN; destruct LNN as (LNN & _ & _).
    unfold wz, PSTAGE2_RET in *.
    unfold mframe in FR.
    eapply rz_step_evt; [exact MOK'|].
    do 12 step.
    replace (ret_pc (Z_to_bv 64 89184)) with (Z_to_bv 64 89184) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step.
    apply evt_done.
    release_frame FR ST (bv_unsigned sp + 80).
    rewrite <- HFS.
    eapply (SO_EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo so code (bv_unsigned tid) _ _ _ _ guard cdt thr sec tm1 ph);
      first [exact MOK'| exact CH1| exact SOF| exact SOB| exact SEF| exact MI| exact LC| exact SSP1| exact SSP2
            | exact D14| exact D15| exact D16
            | exact D2| exact D3| exact D4| exact D5| exact D6| exact D7| exact D8| exact D9| exact D10
            | rewrite Z_to_bv_bv_unsigned; exact D1
            | reflexivity
            | rewrite unsigned_lit by lia; first [exact ST| unfold EXIT_DEPTH; lia]
            | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_die_exit :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (fs : Fs) (FD : list (word * FdEntry)) (lo : Z) (tid : word) (so : stdout_st)
           (cdt thr sec : byte) (tm1 guard : word) (ph : bool),
      DMOD fs FD mo -> (FD = FDS0 \/ exists e, FD = FDS3 e) -> tp = wz PTP ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> GLOBALS_TOP <= lo ->
      DSTAT ph tid m -> 0 < bv_unsigned tid < 2^22 ->
      rw_cells usegs m 0x54c58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m -> ssp_cells m guard ->
      mem_inv usegs m ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x133f4) fc None m (seg_rom usegs)) mo)
               (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz 2) fs)).
  Proof.
    intros until ph. intros DM HFD -> ST LO GT DS TID LC SOF SOB SEF [SSP1 SSP2] MI.
    pose proof DM as [MOK' _ HFS]. destruct (DMOD_chan _ _ _ DM HFD) as [CH1 CH2].
    destruct DS as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16). unfold PDSO, PINCB, PCXAFIN in *.
    unfold wz in *.
    eapply rz_step_evt; [exact MOK'|].
    do 2 step.
    apply evt_done.
    rewrite <- HFS.
    eapply (SO_EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo so 2 (bv_unsigned tid) _ _ _ _ guard cdt thr sec tm1 ph);
      first [exact MOK'| exact CH1| exact SOF| exact SOB| exact SEF| exact MI| exact LC| exact SSP1| exact SSP2
            | exact D14| exact D15| exact D16
            | exact D2| exact D3| exact D4| exact D5| exact D6| exact D7| exact D8| exact D9| exact D10
            | rewrite Z_to_bv_bv_unsigned; exact D1
            | reflexivity
            | exact ST
            | unfold EXIT_DEPTH; lia
            | lia].
  Qed.
End S.


End CeilWrap.
End Drv_exit.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
Module Drv_die.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.UImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.Drv_base Drv_exit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_OOM : so_diag_oom_stmt.
  Hypothesis SO_REFUSED : so_diag_refused_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.
  Hypothesis SO_CANTOPEN : so_diag_cannot_open_stmt.

  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (mo : Model) (fs : Fs) (FD : list (word * FdEntry))
            (lo : Z) (tid : word) (cdt thr sec : byte) (tm1 guard : word).
  Hypothesis DM : DMOD fs FD mo.
  Hypothesis HFD : FD = FDS0 \/ exists e, FD = FDS3 e.
  Hypothesis TP : tp = wz PTP.
  Hypothesis LO : lo + 8192 <= bv_unsigned sp.
  Hypothesis GT : GLOBALS_TOP <= lo.
  Hypothesis SPH : bv_unsigned sp + 64 < 2^63.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.

  (* [comment removed for export] *)
  Definition die_pre (m : word -> option byte) : Prop :=
    stk usegs m lo (bv_unsigned sp) /\ mem_inv usegs m /\ DSTAT false tid m
    /\ rw_cells usegs m 0x54c58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
    /\ ssp_cells m guard /\ stdout_file m stdout_init /\ stderr_wfile0 m.

  Notation ST pc a0 a1 a2 a3 F m := (MS (mkR (wz PSTAGE2_RET) sp gp tp _ _ _ s0 s1 a0 a1 a2 a3 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _) F (wz pc) fc None m (seg_rom usegs)) (only parsing).

  (* [comment removed for export] *)
  Lemma die_tail : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc' : bv 32) (m m' : word -> option byte),
    die_pre m ->
    munch [(lo, bv_unsigned sp); (RSTDERR, RSTDERR + 232)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
    stk usegs m' lo (bv_unsigned sp) -> stderr_file m' -> ssp_cells m' guard ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x133f4) fc' None m' (seg_rom usegs)) mo)
             (t_emit (W 1 []) (t_exit (wz 2) fs)).
  Proof.
    intros until m'. intros (ST & MI & DS & LC & SSP & SOF & SEF) MU WM MI' ST' SEF' SSP'. unfold GLOBALS_TOP in GT.
    change (W 1 []) with (W 1 (to_bytes (so_buf stdout_init))).
    eapply (main_die_exit SO_EXIT) with (lo := lo) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1);
      first [exact DM| exact HFD| exact TP| exact ST'| exact TID| exact MI'| exact SEF'| exact SSP'
            | eapply DSTAT_munch; [exact DS| exact MU| exact WM| constructor; [unfold dstat_safe; cbn [fst snd]; lia| constructor; [unfold dstat_safe; cbn [fst snd]; lia| constructor]]]
            | eapply rw_cells_transport; [exact LC| exact MU| exact WM| cbn; lia]
            | eapply stdout_file_munch; [exact SOF| exact MU| exact WM| constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]]]
            | unfold GLOBALS_TOP, zlength in *; cbn [length so_buf stdout_init Z.of_nat]; lia ].
  Qed.

  (* [comment removed for export] *)
  Local Ltac prep PRE :=
    pose proof PRE as (ST & MI & DS & LC & SSP & SOF & SEF);
    pose proof DS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _); unfold wz in G1, G2;
    pose proof DM as [MOK' _ HFS]; destruct (DMOD_chan _ _ _ DM HFD) as [CH1 CH2];
    unfold GLOBALS_TOP in GT; unfold wz, PSTAGE2_RET.

  (* [comment removed for export] *)
  Lemma die_oom_call : forall (ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_MSG_oom) (wz 19) (wz 1) (wz RSTDERR) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x133f0) fc None m (seg_rom usegs)) mo)
             (t_die msg_oom fs).
  Proof.
    intros until m. intros PRE. prep PRE.
    apply rz_die. eapply rz_step_evt; [exact MOK'|]. step. apply evt_done.
    eapply (SO_OOM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo guard);
      first [exact MOK'| exact CH2| exact SEF| exact ST| exact SSP| exact MI| reflexivity| apply t_emit_has_nil'| unfold FWRITE_DEPTH, GLOBALS_TOP; lia| idtac].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x133f4)) with (Z_to_bv 64 0x133f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply die_tail; [exact PRE| exact MU2| exact WM2| exact MI2| exact ST2| apply stderr_wfile0_file; exact SEF2| exact SSP2].
  Qed.

  (* [comment removed for export] *)
  Lemma die_oom1 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x13414) fc None m (seg_rom usegs)) mo)
             (t_die msg_oom fs).
  Proof.
    intros until m. intros PRE. prep PRE.
    eapply rz_step_evt; [exact MOK'|]. do 8 step. apply evt_done.
    apply (die_oom_call _ _ _ _ _ _ _ _ _ _ _ _ F m PRE).
  Qed.

  (* [comment removed for export] *)
  Lemma die_oom2 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x133d4) fc None m (seg_rom usegs)) mo)
             (t_die msg_oom fs).
  Proof.
    intros until m. intros PRE. prep PRE.
    eapply rz_step_evt; [exact MOK'|]. do 7 step. apply evt_done.
    apply (die_oom_call _ _ _ _ _ _ _ _ _ _ _ _ F m PRE).
  Qed.

  (* [comment removed for export] *)
  Lemma die_refused_call : forall (ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m -> frm0 fc ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz RSTDERR) (wz A_FMT_too_big) (wz 0x4000000) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x133cc) fc None m (seg_rom usegs)) mo)
             (t_die msg_refused fs).
  Proof.
    intros until m. intros PRE FRM. prep PRE.
    apply rz_die. eapply rz_step_evt; [exact MOK'|]. step. apply evt_done.
    eapply (SO_REFUSED _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo guard);
      first [exact MOK'| exact CH2| apply stderr_wfile0_wfile; exact SEF| exact ST| exact SSP| exact MI| exact FRM| reflexivity| apply t_emit_has_nil'| unfold FPRINTF_DEPTH, GLOBALS_TOP; lia| idtac].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m2 MU2 WM2 MI2 FRM2 FA2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x133d0)) with (Z_to_bv 64 0x133d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rz_step_evt; [exact MOK'|]. step. apply evt_done.
    eapply die_tail; [exact PRE| exact MU2| exact WM2| exact MI2| exact ST2| apply stderr_wfile_file; exact SEF2| exact SSP2].
  Qed.

  (* [comment removed for export] *)
  Lemma die_refused : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m -> frm0 fc ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x133b4) fc None m (seg_rom usegs)) mo)
             (t_die msg_refused fs).
  Proof.
    intros until m. intros PRE FRM. prep PRE.
    eapply rz_step_evt; [exact MOK'|]. do 6 step. apply evt_done.
    apply (die_refused_call _ _ _ _ _ _ _ _ _ _ _ _ _ F m PRE FRM).
  Qed.

  (* [comment removed for export] *)
  Lemma die_path_call : forall (fmt : Z) (msg : list byte -> list byte) (SO : so_diag_str_stmt fmt msg)
      (ra t0 t1 t2 p2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte) (P1 : Z) (path slack : list byte),
    die_pre m -> frm0 fc -> p2 = wz P1 ->
    bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 2^20 -> bv_unsigned sp <= P1 ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz RSTDERR) (wz fmt) p2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x133cc) fc None m (seg_rom usegs)) mo)
             (t_die (msg path) fs).
  Proof.
    intros until slack. intros PRE FRM -> BY NONUL SLK LEN PUS. prep PRE.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    apply rz_die. eapply rz_step_evt; [exact MOK'|]. step. apply evt_done.
    eapply (SO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo lo guard path slack);
      first [exact MOK'| exact CH2| apply stderr_wfile0_wfile; exact SEF| exact ST| exact SSP| exact MI| exact FRM| exact NONUL| exact SLK| exact LEN| reflexivity| apply t_emit_has_nil'
            | rewrite ?unsigned_lit by lia; first [exact BY| unfold FPRINTF_DEPTH, GLOBALS_TOP; lia| idtac]].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m2 MU2 WM2 MI2 FRM2 FA2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x133d0)) with (Z_to_bv 64 0x133d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rz_step_evt; [exact MOK'|]. step. apply evt_done.
    eapply die_tail; [exact PRE| exact MU2| exact WM2| exact MI2| exact ST2| apply stderr_wfile_file; exact SEF2| exact SSP2].
  Qed.

  (* [comment removed for export] *)
  Lemma die_readerr : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte) (P1 : Z) (path slack : list byte),
    die_pre m -> frm0 fc -> s2 = wz P1 ->
    bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 2^20 -> bv_unsigned sp <= P1 ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x13398) fc None m (seg_rom usegs)) mo)
             (t_die (msg_read_error path) fs).
  Proof.
    intros until slack. intros PRE FRM S2 BY NONUL SLK LEN PUS. prep PRE.
    eapply rz_step_evt; [exact MOK'|]. do 7 step. apply evt_done.
    apply (die_path_call A_FMT_read_error msg_read_error SO_READERR _ _ _ _ _ _ _ _ _ _ _ _ _ _ F m P1 path slack PRE FRM S2 BY NONUL SLK LEN PUS).
  Qed.

  Lemma die_cantopen : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte) (P1 : Z) (path slack : list byte),
    die_pre m -> frm0 fc -> s2 = wz P1 ->
    bytes_at usegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 2^20 -> bv_unsigned sp <= P1 ->
    realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x133fc) fc None m (seg_rom usegs)) mo)
             (t_die (msg_cannot_open path) fs).
  Proof.
    intros until slack. intros PRE FRM S2 BY NONUL SLK LEN PUS. prep PRE.
    eapply rz_step_evt; [exact MOK'|]. do 8 step. apply evt_done.
    apply (die_path_call A_FMT_cannot_open msg_cannot_open SO_CANTOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ F m P1 path slack PRE FRM S2 BY NONUL SLK LEN PUS).
  Qed.
End S.


End CeilWrap.
End Drv_die.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree F_pad Exit F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.SO_piface.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import Drv_base.
Import Drv_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import SspGuard.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_USAGE : so_diag_usage_stmt.

  Lemma main_usage :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model)
           (fs : Fs) (lo argc P0 : Z) (tid : word) (argv0 slack : list byte) (guard : word) (cdt thr sec : byte) (tm1 : word),
      DMOD fs FDS0 mo ->
      ra = wz PSTAGE2_RET -> tp = wz PTP -> a0 = wz argc -> a1 = wz (bv_unsigned sp + 56) ->
      0 <= argc < 2^63 -> argc <> 2 ->
      stk usegs m lo (bv_unsigned sp) -> lo + 2^20 <= bv_unsigned sp -> GLOBALS_TOP <= lo -> bv_unsigned sp + 80 < 2^63 ->
      mem_inv usegs m -> frm0 fc ->
      DSTAT false tid m -> 0 < bv_unsigned tid < 2^22 ->
      rw_cells usegs m 0x54c58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
      ssp_cells m guard ->
      stdout_file m stdout_init -> stderr_wfile0 m ->
      rw_cells usegs m (bv_unsigned sp + 56) [C8 (wz P0)] ->
      bytes_at usegs m P0 (argv0 ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) argv0 ->
      (- (P0 + zlength argv0 + 1)) mod 8 <= zlength slack -> zlength argv0 <= 2^20 -> bv_unsigned sp <= P0 ->
      realizes usegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz PMAIN) fc None m (seg_rom usegs)) mo)
               (t_die (msg_usage argv0) fs).
  Proof.
    intros until tm1. intros DM RA TP -> -> ARG ARG2 ST LO GT SPH MI FRM DS TID LC SSP SOF SEF AV BY NONUL SLK LEN PUS.
    pose proof DM as [MOK' _ HFS]. destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    unfold GLOBALS_TOP in GT. unfold wz, PMAIN in *.
    apply rz_die.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    eapply rz_step_evt; [exact MOK'|].
    carve_frame 80%nat ST.
    do 12 step.
    if_cases K; zify_cond K; [| exfalso; lia]. clear K.
    lazymatch type of MU with munch _ _ ?mm => rename mm into m1 end.   (* [comment removed for export] *)
    assert (DS1 : DSTAT false tid m1).
    { eapply DSTAT_munch; [exact DS| exact MU| exact WM| constructor; [unfold dstat_safe; cbn [fst snd]; lia| constructor]]. }
    pose proof DS1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _). unfold wz in G1, G2.
    do 7 step.
    apply evt_done.
    assert (SEF1 : stderr_wfile m1).
    { apply stderr_wfile0_wfile. eapply stderr_wfile0_munch; [exact SEF| exact MU| exact WM| constructor; [cbn [fst snd]; lia| constructor]]. }
    assert (SSP1 : ssp_cells m1 guard).
    { destruct SSP as [S1 S2]. split;
      [ (eapply rw_cells_transport; [exact S1| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard; lia])
      | (eapply rw_cells_transport; [exact S2| exact MU| exact WM| cbn; unfold got_ssp, ssp_guard; lia]) ]. }   (* [comment removed for export] *)
    eapply (SO_USAGE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 mo lo guard argv0 slack);
      first [exact MOK'| exact CH2| exact SEF1| exact BY| exact NONUL| exact SLK| exact LEN| exact MI| exact FRM| exact SSP1| reflexivity| apply t_emit_has_nil'
            | rewrite ?unsigned_lit by lia; first [exact ST| exact BY| unfold FPRINTF_DEPTH, GLOBALS_TOP; lia | idtac] ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m2 MU2 WM2 MI2 FRM2 FA2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 78624)) with (Z_to_bv 64 78624) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rz_step_evt; [exact MOK'|].
    step. apply evt_done.
    rewrite RA in FR.
    assert (DS2 : DSTAT false tid m2).
    { eapply DSTAT_munch; [exact DS1| exact MU2| exact WM2| constructor; [unfold dstat_safe; cbn [fst snd]; lia| constructor; [unfold dstat_safe; cbn [fst snd]; lia| constructor]]]. }
    change (W 1 []) with (W 1 (to_bytes (so_buf stdout_init))).
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?fj0 :: _) =>
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -80) (mframe fj0 s0 s1 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 PSTAGE2_RET)))
        by (unfold mframe; eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn; lia]) end.
    assert (LC2 : rw_cells usegs m2 0x54c58 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]).
    { eapply rw_cells_transport; [exact LC| exact MU2| exact WM2| cbn; lia]. }
    assert (SOF2 : stdout_file m2 stdout_init).
    { eapply stdout_file_munch; [| exact MU2| exact WM2| constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]]].
      eapply stdout_file_munch; [exact SOF| exact MU| exact WM| constructor; [cbn [fst snd]; lia| constructor]]. }
    eapply (main_epilogue_exit SO_EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ft fc' m2 mo fs FDS0 lo 2 tid stdout_init
              _ s0 s1 s2 s3 s4 s5 s6 s7 cdt thr sec tm1 guard);
      rewrite ?unsigned_lit by lia;
      first [exact DM| left; reflexivity| reflexivity| exact TP| exact MI2| exact SSP2| exact DS2| exact TID| exact FR2| exact LC2| exact SOF2| exact ST2
            | apply stderr_wfile_file; exact SEF2
            | unfold GLOBALS_TOP, zlength in *; cbn; lia ].
  Qed.
End S.


End CeilWrap.
