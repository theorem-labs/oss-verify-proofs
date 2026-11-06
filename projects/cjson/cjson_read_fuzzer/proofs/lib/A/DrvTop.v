(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require SO_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit_pre2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_trunA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_icpt_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_dicpt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
Module Drv_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Variable AI : art_iface.
  Let ART := CJ_iface.ART AI.
  Hypothesis SO_EXIT : so_exit_stmt.

  (* [comment removed for export] *)
  Lemma exit_call :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (fs : Fs) (FD : list (word * FdEntry)) (lo code : Z) (tid : word) (so : stdout_st)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B : Z),
      DMOD fs FD mo -> (FD = FDS0 \/ exists e, FD = FDS3 e) ->
      a0 = wz code -> 0 <= code < 256 -> tp = wz ATP ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AEXIT_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
      ART sp0 SPB LB [] TRS B m mo g ->
      ADSTAT tid m -> 0 < bv_unsigned tid < 2^22 ->
      stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m -> stdin_file m ->
      mem_inv asegs m ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz AEXITF) fc None m (seg_rom asegs)) mo g
          (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz code) fs)).
  Proof.
    intros until B. intros DM HFD Ha0 CODE TP ST CEIL LO SPH HART DS TID SOF SOB SEF SIF MI.
    pose proof DM as [_ HFS _]. destruct (DMOD_chan _ _ _ DM HFD) as [CH1 CH2].
    pose proof (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) as (IC & PC & FMC & IC2 & UC & UC2 & (XG & XN & XR & XM)).
    destruct (art_exit_shadows m (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART)) as ([jA SA] & [jB SB] & [jC SC] & [jD SD]).
    destruct DS as (D1 & D2 & (cdt & thr & sec & tm1 & D3) & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11
                    & D12 & D13 & D14 & D15 & D16 & D17 & D18 & (cn0 & D19)).
    rewrite <- HFS.
    eapply (SO_EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g lo so code (bv_unsigned tid)
              cdt thr sec tm1 jA jB jC jD cn0);
      first [ exact CH1 | exact ST | exact CEIL | exact LO | exact SPH | exact TP | exact Ha0 | exact CODE | exact TID
            | rewrite Z_to_bv_bv_unsigned; exact D1
            | exact D2 | exact D3 | exact D4 | exact D5 | exact D8
            | exact XG | exact UC | exact UC2 | exact IC | exact PC | exact XN | exact XR | exact XM
            | exact SA | exact SB | exact SC | exact SD
            | exact D12 | exact D13 | exact D14 | exact D15 | exact SOF | exact SOB | exact SEF | exact SIF | exact D18 | exact D19 | exact MI
            | split; [exact (proj1 D6)| split; [exact (proj1 D7)| split; [exact (proj1 D9)| split; [exact (proj1 D10)| exact (proj1 D11)]]]] ].
  Qed.

  (* [comment removed for export] *)
  Lemma main_epilogue_exit :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (fs : Fs) (FD : list (word * FdEntry)) (lo code : Z) (tid : word) (so : stdout_st)
           (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B : Z),
      DMOD fs FD mo -> (FD = FDS0 \/ exists e, FD = FDS3 e) ->
      s0 = wz code -> 0 <= code < 256 -> tp = wz ATP ->
      rw_cells asegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 (wz ASTAGE2_RET)) ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AEXIT_DEPTH <= bv_unsigned sp -> bv_unsigned sp + 80 < 2^47 ->
      ART sp0 SPB LB [] TRS B m mo g ->
      ADSTAT tid m -> 0 < bv_unsigned tid < 2^22 ->
      stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m -> stdin_file m ->
      mem_inv asegs m ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x820b4) fc None m (seg_rom asegs)) mo g
          (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz code) fs)).
  Proof.
    intros until B. intros DM HFD -> CODE TP FR ST CEIL LO SPH HART DS TID SOF SOB SEF SIF MI.
    pose proof ST as LNN; destruct LNN as (LNN & _ & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold mframe in FR. unfold wz, ASTAGE2_RET in *. try rewrite alloc_ceiling_lit in CEIL. unfold AEXIT_DEPTH, AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH in LO.
    apply lrz_step_evt.
    do 12 step.
    replace (ret_pc (Z_to_bv 64 580376)) with (Z_to_bv 64 580376 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step.                                   (* [comment removed for export] *)
    apply evt_done.
    release_frame FR ST (bv_unsigned sp + 80).
    eapply exit_call with (lo := lo) (tid := tid);
      first [ exact DM | exact HFD | reflexivity | exact CODE | exact TP | exact HART | exact DS | exact TID | exact SOF | exact SOB | exact SEF | exact SIF | exact MI
            | rewrite ?unsigned_lit by lia; first [exact ST | try rewrite alloc_ceiling_lit; lia | unfold AEXIT_DEPTH, AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH; lia | lia] ].
  Qed.

  (* [comment removed for export] *)
  Lemma main_die_exit :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (fs : Fs) (FD : list (word * FdEntry)) (lo : Z) (tid : word) (so : stdout_st)
           (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B : Z),
      DMOD fs FD mo -> (FD = FDS0 \/ exists e, FD = FDS3 e) -> tp = wz ATP ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AEXIT_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
      ART sp0 SPB LB [] TRS B m mo g ->
      ADSTAT tid m -> 0 < bv_unsigned tid < 2^22 ->
      stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m -> stdin_file m ->
      mem_inv asegs m ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x82140) fc None m (seg_rom asegs)) mo g
          (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz 2) fs)).
  Proof.
    intros until B. intros DM HFD TP ST CEIL LO SPH HART DS TID SOF SOB SEF SIF MI.
    unfold wz in *.
    apply lrz_step_evt.
    do 2 step.
    apply evt_done.
    eapply exit_call with (lo := lo) (tid := tid);
      first [ exact DM | exact HFD | reflexivity | exact TP | exact ST | exact CEIL | exact LO | exact SPH | exact HART | exact DS | exact TID
            | exact SOF | exact SOB | exact SEF | exact SIF | exact MI | lia ].
  Qed.
End S.


End CeilWrap.
End Drv_exit.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
Module Drv_die.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art Drv_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Variable AI : art_iface.
  Let ART := CJ_iface.ART AI.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_OOM : so_diag_oom_stmt.
  Hypothesis SO_REFUSED : so_diag_refused_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.
  Hypothesis SO_CANTOPEN : so_diag_cannot_open_stmt.

  Variables (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (mo : Model) (g : lghost) (fs : Fs) (FD : list (word * FdEntry))
            (lo : Z) (tid : word) (sp0 SPB : Z) (LB : list cblock) (TRS : list (list Z)) (B : Z).
  Hypothesis DM : DMOD fs FD mo.
  Hypothesis HFD : FD = FDS0 \/ exists e, FD = FDS3 e.
  Hypothesis TP : tp = wz ATP.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + 16384 <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp + 128 <= 2^47.
  Hypothesis SPBE : bv_unsigned sp <= SPB.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.
  Hypothesis FRM : frm0 fc.

  (* [comment removed for export] *)
  Definition die_pre (m : word -> option byte) : Prop :=
    stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m /\ ADSTAT tid m /\ DICPT m
    /\ stdout_file m stdout_init /\ stderr_wfile0 m /\ stdin_file m /\ stack_shadow_zero m
    /\ ART sp0 SPB LB [] TRS B m mo g.

  (* [comment removed for export] *)
  Local Ltac ivs := unfold adstat_easy, AIMG_HI, AERRNO, AINITFLAG, ATP; exit_lits; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

  Lemma die_tail : forall (K : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc' : bv 32) (m m' : word -> option byte),
    die_pre m -> 0 <= K <= 16384 ->
    munch [(bv_unsigned sp - K, bv_unsigned sp); (ASTDERR, ASTDERR + 232)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    stk asegs m' lo (bv_unsigned sp) -> stderr_file m' ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x82140) fc' None m' (seg_rom asegs)) mo g
        (t_emit (W 1 []) (t_exit (wz 2) fs)).
  Proof.
    intros until m'. intros (ST & MI & DS & DI & SOF & SEF & SIF & SSZ & HART) HK MU WM MI' ST' SEF'.
    pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE.
    change (W 1 []) with (W 1 (to_bytes (so_buf stdout_init))).
    eapply (main_die_exit AI SO_EXIT) with (lo := lo) (tid := tid) (sp0 := sp0) (SPB := SPB) (LB := LB) (TRS := TRS) (B := B);
      [ exact DM | exact HFD | exact TP | exact ST' | exact CEIL | unfold AEXIT_DEPTH, AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH; lia | lia
      | | | exact TID | | unfold zlength; cbn [length so_buf stdout_init Z.of_nat]; lia | exact SEF' | | exact MI' ].
    - eapply (art_frame AI); [exact HART | exact MU | exact WM |].
      apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit|]; lia | apply Forall_cons; [apply cj_write_ok_stderr | apply Forall_nil]].
    - eapply ADSTAT_munch_easy; [exact DS | exact MU | exact WM | ivs].
    - eapply stdout_file_munch; [exact SOF | exact MU | exact WM | ivs].
    - eapply stdin_file_munch; [exact SIF | exact MU | exact WM | ivs].
  Qed.

  (* [comment removed for export] *)
  Local Ltac prep PRE :=
    pose proof PRE as (ST & MI & DS & DI & SOF & SEF & SIF & SSZ & HART);
    pose proof DS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _);
    unfold wz, AGOT_STDERR, ASTDERR_VAR in G1, G2; revert G1 G2; exit_lits; intros G1 G2;
    destruct (DMOD_chan _ _ _ DM HFD) as [CH1 CH2];
    pose proof CEIL as CE; try rewrite alloc_ceiling_lit in CE;
    unfold wz.

  (* [comment removed for export] *)
  Lemma die_oom_call : forall (ra t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_MSG_oom) (wz 19) (wz 1) (wz ASTDERR) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x8213c) fc None m (seg_rom asegs)) mo g
        (t_die msg_oom fs).
  Proof.
    intros until m. intros PRE. prep PRE.
    pose proof (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) as (IC & PC & FMC & IC2 & UC & UC2 & XC).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART) as LOW.
    destruct (ADSTAT_ssp tid m DS) as (cn0 & SSP & ASSP).
    apply lrz_die. apply lrz_step_evt. step. apply evt_done.
    eapply (SO_OOM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g lo cn0);
      first [ exact CH2 | exact SEF | exact IC | exact (DICPT_fwrite m DI) | exact LOW | exact ST | exact CEIL | exact SSP | exact MI
            | reflexivity | apply t_emit_has_nil' | unfold AFWRITE_STACK; lia | idtac ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x82140)) with (Z_to_bv 64 0x82140 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (die_tail AFWRITE_STACK); [exact PRE| unfold AFWRITE_STACK; lia| exact MU2| exact WM2| exact MI2| exact ST2| apply stderr_wfile0_file; exact SEF2].
  Qed.

  (* [comment removed for export] *)
  Lemma die_oom1 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x82160) fc None m (seg_rom asegs)) mo g
        (t_die msg_oom fs).
  Proof.
    intros until m. intros PRE. prep PRE.
    apply lrz_step_evt. do 8 step. apply evt_done.
    apply (die_oom_call _ _ _ _ _ _ _ _ _ _ _ _ F m PRE).
  Qed.

  (* [comment removed for export] *)
  Lemma die_oom2 : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x82120) fc None m (seg_rom asegs)) mo g
        (t_die msg_oom fs).
  Proof.
    intros until m. intros PRE. prep PRE.
    apply lrz_step_evt. do 7 step. apply evt_done.
    apply (die_oom_call _ _ _ _ _ _ _ _ _ _ _ _ F m PRE).
  Qed.

  (* [comment removed for export] *)
  Lemma die_fmt_facts : forall m, die_pre m -> fmt_cells m /\ MRT m /\ lowsh_at m /\ exists cn0 : word, assp_cells m cn0.
  Proof.
    intros m (ST & MI & DS & DI & SOF & SEF & SIF & SSZ & HART).
    pose proof (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) as (IC & PC & FMC & IC2 & UC & UC2 & XC).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART) as LOW.
    destruct (ADSTAT_ssp tid m DS) as (cn0 & SSP & ASSP).
    split; [exact FMC|]. split; [apply drv_MRT; [exact IC| exact IC2| exact SSZ| exact LOW]|]. split; [exact LOW| exists cn0; exact ASSP].
  Qed.

  (* [comment removed for export] *)
  Lemma die_refused_call : forall (ra t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz ASTDERR) (wz A_FMT_too_big) (wz 0x4000000) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x82118) fc None m (seg_rom asegs)) mo g
        (t_die msg_refused fs).
  Proof.
    intros until m. intros PRE. prep PRE. destruct (die_fmt_facts m PRE) as (FMC & MR & LOW & (cn0 & ASSP)).
    apply lrz_die. apply lrz_step_evt. step. apply evt_done.
    eapply (SO_REFUSED _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g lo cn0);
      first [ exact CH2 | apply stderr_wfile0_wfile; exact SEF | exact FMC | exact MR | exact LOW | exact ST | exact CEIL | exact ASSP | exact MI | exact FRM
            | reflexivity | apply t_emit_has_nil' | unfold AFPRINTF_STACK; lia | lia | idtac ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m2 MU2 WM2 MI2 FRM2 FA2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x8211c)) with (Z_to_bv 64 0x8211c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply lrz_step_evt. step. apply evt_done.
    eapply (die_tail AFPRINTF_STACK); [exact PRE| unfold AFPRINTF_STACK; lia| exact MU2| exact WM2| exact MI2| exact ST2| apply stderr_wfile_file; exact SEF2].
  Qed.

  (* [comment removed for export] *)
  Lemma die_refused : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte),
    die_pre m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x82100) fc None m (seg_rom asegs)) mo g
        (t_die msg_refused fs).
  Proof.
    intros until m. intros PRE. prep PRE.
    apply lrz_step_evt. do 6 step. apply evt_done.
    apply (die_refused_call _ _ _ _ _ _ _ _ _ _ _ _ _ F m PRE).
  Qed.

  (* [comment removed for export] *)
  Lemma die_path_call : forall (fmt : Z) (msg : list byte -> list byte) (SO : so_diag_str_stmt fmt msg)
      (ra t0 t1 t2 p2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte) (P1 : Z) (path slack : list byte),
    die_pre m -> p2 = wz P1 ->
    bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 2^20 -> bv_unsigned sp <= P1 ->
    P1 + zlength path + 1 + zlength slack + 16 <= 2^47 ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz ASTDERR) (wz fmt) p2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x82118) fc None m (seg_rom asegs)) mo g
        (t_die (msg path) fs).
  Proof.
    intros until slack. intros PRE -> BY NONUL SLK LEN PUS PHI. prep PRE. destruct (die_fmt_facts m PRE) as (FMC & MR & LOW & (cn0 & ASSP)).
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    apply lrz_die. apply lrz_step_evt. step. apply evt_done.
    eapply (SO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g lo cn0 path slack);
      first [ exact CH2 | apply stderr_wfile0_wfile; exact SEF | exact FMC | exact MR | exact LOW | exact ST | exact CEIL | exact ASSP | exact MI | exact FRM
            | exact NONUL | exact SLK | exact LEN | reflexivity | apply t_emit_has_nil'
            | rewrite ?unsigned_lit by lia; first [exact BY | exact PUS | exact PHI | unfold AFPRINTF_STACK; lia | lia | idtac] ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m2 MU2 WM2 MI2 FRM2 FA2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x8211c)) with (Z_to_bv 64 0x8211c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply lrz_step_evt. step. apply evt_done.
    eapply (die_tail AFPRINTF_STACK); [exact PRE| unfold AFPRINTF_STACK; lia| exact MU2| exact WM2| exact MI2| exact ST2| apply stderr_wfile_file; exact SEF2].
  Qed.

  (* [comment removed for export] *)
  Lemma die_readerr : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte) (P1 : Z) (path slack : list byte),
    die_pre m -> s2 = wz P1 ->
    bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 2^20 -> bv_unsigned sp <= P1 ->
    P1 + zlength path + 1 + zlength slack + 16 <= 2^47 ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x820e4) fc None m (seg_rom asegs)) mo g
        (t_die (msg_read_error path) fs).
  Proof.
    intros until slack. intros PRE S2 BY NONUL SLK LEN PUS PHI. prep PRE.
    apply lrz_step_evt. do 7 step. apply evt_done.
    apply (die_path_call A_FMT_read_error msg_read_error SO_READERR _ _ _ _ _ _ _ _ _ _ _ _ _ _ F m P1 path slack PRE S2 BY NONUL SLK LEN PUS PHI).
  Qed.

  Lemma die_cantopen : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (m : word -> option byte) (P1 : Z) (path slack : list byte),
    die_pre m -> s2 = wz P1 ->
    bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
    (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 2^20 -> bv_unsigned sp <= P1 ->
    P1 + zlength path + 1 + zlength slack + 16 <= 2^47 ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x82148) fc None m (seg_rom asegs)) mo g
        (t_die (msg_cannot_open path) fs).
  Proof.
    intros until slack. intros PRE S2 BY NONUL SLK LEN PUS PHI. prep PRE.
    apply lrz_step_evt. do 8 step. apply evt_done.
    apply (die_path_call A_FMT_cannot_open msg_cannot_open SO_CANTOPEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ F m P1 path slack PRE S2 BY NONUL SLK LEN PUS PHI).
  Qed.
End S.


End CeilWrap.
End Drv_die.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_stmt.
Module Drv_usage.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art Drv_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Variables (AI : art_iface) (TI : trs_iface).
  Let ART := CJ_iface.ART AI.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_USAGE : so_diag_usage_stmt.

  Local Ltac ivs := unfold adstat_easy, AIMG_HI, AERRNO, AINITFLAG, ATP; exit_lits; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

  Theorem main_usage : main_usage_stmt AI TI.
  Proof.
    unfold main_usage_stmt. intros until B0.
    intros DM HART _ _ RA TP -> -> ARG ARG2 ST LO CEIL SPH SPAL MI FRM DS TID DI SOF SEF SIF SSZ AV BY NONUL SLK LEN PUS PHI.
    destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    unfold wz, AMAIN in *.
    apply lrz_die.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply lrz_step_evt.
    carve_frame 80%nat ST.
    do 12 step.
    if_cases K; zify_cond K; [| exfalso; lia]. clear K.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (DS1 : ADSTAT tid m1) by (eapply ADSTAT_munch_easy; [exact DS| exact MU| exact WM| ivs]);
      assert (DI1 : DICPT m1) by (eapply DICPT_munch; [exact DI| exact MU| exact WM| repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil]);
      assert (SOF1 : stdout_file m1 stdout_init) by (eapply stdout_file_munch; [exact SOF| exact MU| exact WM| ivs]);
      assert (SEF1 : stderr_wfile0 m1) by (destruct SEF as (fl & md & e & we & tl & FC & R); exists fl, md, e, we, tl; split; [| exact R];
                                            eapply rw_cells_transport; [exact FC| exact MU| exact WM| exit_lits; cbn; lia]);
      assert (SIF1 : stdin_file m1) by (eapply stdin_file_munch; [exact SIF| exact MU| exact WM| ivs]);
      assert (SSZ1 : stack_shadow_zero m1) by (eapply stack_shadow_zero_munch; [exact SSZ| exact MU|]; apply Forall_cons; [cbn [fst snd]; unfold SSZ_HI; split; lia | apply Forall_nil]);
      assert (HART1 : ART (bv_unsigned sp + 48) (bv_unsigned sp) [] [] [] B0 m1 mo g)
        by (eapply (art_frame AI); [exact HART| exact MU| exact WM| apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit|]; lia| apply Forall_nil]])
    end.
    pose proof DS1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _).
    unfold wz, AGOT_STDERR, ASTDERR_VAR in G1, G2. revert G1 G2. exit_lits. intros G1 G2.
    do 7 step.
    apply evt_done.
    (* [comment removed for export] *)
    pose proof (artcells_split _ (art_rtcells AI _ _ _ _ _ _ _ _ _ HART1)) as (IC & PC & FMC & IC2 & UC & UC2 & XC).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART1) as LOW.
    destruct (ADSTAT_ssp tid _ DS1) as (cn0 & SSP & ASSP).
    pose proof (drv_MRT _ IC IC2 SSZ1 LOW) as MR.
    lazymatch goal with |- LRZ _ (MS _ _ _ _ _ ?m1 _) _ _ _ =>
      lazymatch goal with STx : stk asegs m1 lo _ |- _ =>
      eapply (SO_USAGE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 mo g lo cn0 argv0 slack);
      first [ exact CH2 | apply stderr_wfile0_wfile; exact SEF1 | exact FMC | exact MR | exact LOW | exact ASSP | assumption | exact FRM
            | exact NONUL | exact SLK | reflexivity | apply t_emit_has_nil'
            | rewrite ?unsigned_lit by lia; first [exact BY | exact STx | unfold AFPRINTF_STACK; lia | lia | idtac] ]
      end end.
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m2 MU2 WM2 MI2 FRM2 FA2 ST2 SEF2 SSP2.
    rewrite unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x8206c)) with (Z_to_bv 64 0x8206c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply lrz_step_evt. step. apply evt_done.
    rewrite RA in FR.
    change (W 1 []) with (W 1 (to_bytes (so_buf stdout_init))).
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?fj0 :: _) =>
      assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -80) (mframe fj0 s0 s1 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 ASTAGE2_RET)))
        by (unfold mframe; eapply rw_cells_transport; [exact FR| exact MU2| exact WM2| cbn; unfold AFPRINTF_STACK; exit_lits; lia]) end.
    eapply (main_epilogue_exit AI SO_EXIT) with (lo := lo) (tid := tid) (code := 2);
      rewrite ?unsigned_lit by lia;
      first [ exact DM | left; reflexivity | reflexivity | exact TP | exact FR2 | exact ST2 | exact CEIL | exact TID | exact MI2
            | apply stderr_wfile_file; exact SEF2
            | eapply (art_frame AI); [exact HART1 | exact MU2 | exact WM2
                                     | apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit|]; unfold AFPRINTF_STACK; lia | apply Forall_cons; [apply cj_write_ok_stderr | apply Forall_nil]]]
            | eapply ADSTAT_munch_easy; [exact DS1 | exact MU2 | exact WM2 | unfold AFPRINTF_STACK in *; ivs]
            | eapply stdout_file_munch; [exact SOF1 | exact MU2 | exact WM2 | unfold AFPRINTF_STACK in *; ivs]
            | eapply stdin_file_munch; [exact SIF1 | exact MU2 | exact WM2 | unfold AFPRINTF_STACK in *; ivs]
            | rewrite ?unsigned_lit by lia; unfold AEXIT_DEPTH, AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH, AFPRINTF_STACK, zlength in *; cbn [length so_buf stdout_init Z.of_nat]; lia ].
  Qed.
End S.


End CeilWrap.
End Drv_usage.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_syscalls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_hooks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require SspGuard.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module Drv_hdr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.LRzAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art Drv_exit Drv_die OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_xport OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_hooks.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.SspGuard.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil} {AGRD : Guard}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma t_emit_app' : forall o1 o2 K, t_eq (t_emit (o1 ++ o2) K) (t_emit o1 (t_emit o2 K)).
Proof.
  intros o1 o2 K tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HK)].
    + destruct (is_prefix_app_split o1 o2 tr Hp) as [Hp1 | (b' & -> & Hp2)]; [left; exact Hp1|].
      right. exists b'. split; [reflexivity|]. left. exact Hp2.
    + right. exists (o2 ++ tr'). split; [rewrite app_assoc; reflexivity|]. right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp2 | (tr'' & -> & HK)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. clear K. revert o2 tr' Hp2. induction o1 as [|x o1 IH]; intros o2 tr' Hp2; cbn; [exact Hp2|]. split; [reflexivity| apply IH; exact Hp2].
    + right. exists tr''. split; [rewrite app_assoc; reflexivity| exact HK].
Qed.

Lemma t_eq_alt2 : forall A A' B B' : TSet, t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.

Lemma lines_length : forall j, zlength (lines j) = 2 * Z.of_nat j.
Proof. intros j. unfold lines, zlength. induction j as [|j IH]; [reflexivity|]. cbn [repeat concat app length]. lia. Qed.

Lemma zero_lines_eq : forall n, to_bytes (concat (repeat [48; 10] n)) = zero_lines n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat concat app]. cbn. rewrite <- IH. reflexivity. Qed.

Lemma zero_lines_S : forall j, zero_lines (S j) = emit_line ++ to_bytes (lines j).
Proof. intros j. unfold lines. rewrite zero_lines_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cfg_decode : forall b0 b1 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sxb b1)) 57))) 49))) (bv_unsigned (zxb b0))
  = (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768.
Proof.
  intros b0 b1.
  pose proof (bv_unsigned_in_range 8 b0) as R0. change (bv_modulus 8) with 256 in R0.
  pose proof (bv_unsigned_in_range 8 b1) as R1. change (bv_modulus 8) with 256 in R1.
  unfold sxb, zxb. rewrite !Z_to_bv_unsigned.
  set (r := bv_unsigned b1 mod 128).
  assert (Hr : 0 <= r < 128) by (subst r; apply Z.mod_pos_bound; lia).
  assert (U : exists q, bv_wrap 64 (bv_signed b1) = 128 * q + r /\ 0 <= q).
  { unfold bv_wrap, bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128. change (2 ^ Z.of_N 64) with 18446744073709551616.
    destruct (Z_lt_dec (bv_unsigned b1) 128).
    - exists (bv_unsigned b1 / 128). rewrite (Z.mod_small (bv_unsigned b1 + 128)) by lia.
      rewrite Z.mod_small by lia. subst r. split; [| apply Z.div_pos; lia]. rewrite <- Z.div_mod by lia. lia.
    - exists ((18446744073709551616 - 256) / 128 + bv_unsigned b1 / 128).
      replace (bv_unsigned b1 + 128) with ((bv_unsigned b1 - 128) + 1 * 256) by lia. rewrite Z.mod_add, (Z.mod_small (bv_unsigned b1 - 128)) by lia.
      replace (bv_unsigned b1 - 128 - 128) with ((18446744073709551616 - 256 + bv_unsigned b1) + (-1) * 18446744073709551616) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. subst r.
      pose proof (Z.div_mod (bv_unsigned b1) 128 ltac:(lia)). split; [| lia].
      change ((18446744073709551616 - 256) `div` 128) with 144115188075855870. lia. }
  (nelim U 3%nat; intros q -> Hq).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace ((128 * q + r) * 2 ^ 57) with (r * 2 ^ 57 + q * 2 ^ 64) by lia.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (r * 2 ^ 57)) by lia.
  replace (r * 2 ^ 57) with (r * 2 ^ 8 * 2 ^ 49) by lia. rewrite Z.div_mul by lia.
  rewrite (Z.mod_small (r * 2 ^ 8)) by lia. rewrite (Z.mod_small (bv_unsigned b0)) by lia.
  replace (r * 2 ^ 8) with (Z.shiftl r 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  subst r. rewrite <- (Z.mod_small (bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128)) 32768).
  2:{ pose proof (Z.mod_pos_bound (bv_unsigned b1) 128). lia. }
  replace 32768 with (256 * 128) by reflexivity.
  rewrite <- (Z.mod_add _ (bv_unsigned b1 / 128)) by lia. f_equal.
  pose proof (Z.div_mod (bv_unsigned b1) 128 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma t_body_run : forall data fs (b0 b1 : byte) (cl len : Z),
  nth_error data 0 = Some b0 -> nth_error data 1 = Some b1 ->
  len = zlength data -> cl = (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768 ->
  len < MAX_INPUT -> 6 + cl <= len ->
  t_body data fs = t_emit (W 1 (zero_lines (tcalls cl data))) (t_exit (exit_code 0) fs).
Proof.
  intros data fs b0 b1 cl len H0 H1 HL HC MX OV.
  pose proof (bv_unsigned_in_range 8 b0) as R0. change (bv_modulus 8) with 256 in R0.
  pose proof (bv_unsigned_in_range 8 b1) as R1. change (bv_modulus 8) with 256 in R1.
  assert (Hcl : 0 <= cl < 32768) by (subst cl; apply Z.mod_pos_bound; lia).
  unfold t_body. subst len. unfold zlength in *.
  replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; lia).
  replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  rewrite (nth_error_nth _ _ _ H0), (nth_error_nth _ _ _ H1). cbv zeta. rewrite <- HC.
  replace (length data <? 6 + Z.to_nat cl)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  unfold tcalls. reflexivity.
Qed.

Lemma tcalls_S : forall cl data, exists j : nat, tcalls cl data = S j /\ (j <= 3)%nat.
Proof.
  intros cl data. unfold tcalls. destruct (Z.to_nat cl).
  - exists 0%nat. split; [reflexivity| lia].
  - eexists. split; [reflexivity|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 data (Z_to_bv 8 0))) 4 ltac:(lia)). lia.
Qed.

Section S.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface).
  Let ART := CJ_iface.ART AI.
  Let ADRV := Drv_iface2.ADRV AI DI.
  Hypothesis TROK : drv_traces_ok TI.
  Hypothesis NPOK : 4 * FUZZ_NP (2^26) <= NPMAX TI.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_SHORT : so_diag_short_stmt.
  Hypothesis SO_OVERRUN : so_diag_overrun_stmt.

  (* [comment removed for export] *)
  Definition trun_all : Prop :=
    forall sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap,
      trun_side sp tp lo SPB -> trun_stmt AI DI TI sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap.
  Hypothesis TRUN : trun_all.

  Variables (sp gp tp : word) (fs : Fs) (lo SPB P1 : Z) (tid : word)
            (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (q8 q9 q10 q11 : word).
  Hypothesis TP : tp = wz ATP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 2^47.
  Hypothesis SPBE : SPB = bv_unsigned sp + 80.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis WIN : sp_window_lo <= bv_unsigned sp + 128.
  Hypothesis BOT : ASTACK_BOTTOM (bv_unsigned sp + 128) <= lo.

  Lemma CEIL : alloc_ceiling <= lo. Proof. try rewrite alloc_ceiling_lit. exact GT. Qed.

  Notation FRAME m := (rw_cells asegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 (wz ASTAGE2_RET))).

  (* [comment removed for export] *)
  Lemma main_free_exit : forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost) (LB : list cblock) (TRS : list (list Z)) (B np A cap code : Z)
      (so : stdout_st) (e : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word),
    ART (bv_unsigned sp + 128) SPB LB [] TRS B m mo g -> In (A, cap) LB -> TINV TI np TRS -> cost_free <= B -> DMOD fs FDS0 mo -> 0 <= code < 256 ->
    rw_cells asegs m AERRNO [C4 e] -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> FRAME m ->
    ADSTAT tid m -> DICPT m -> stdout_file m so -> zlength (so_buf so) <= 8 -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz code) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                  F (wz 0x820ac) fc None m (seg_rom asegs)) mo g
        (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz code) fs)).
  Proof.
    intros until t6. intros HART INA HT HB DM CODE ER MI ST FR DS DIC SOF SOB SEF SIF SSZ.
    unfold wz in *. unfold AERRNO, ATP in ER.
    apply lrz_step_evt. do 2 step. apply evt_done.
    eapply (drv_free AI TI TROK) with (lo := lo) (np := np) (A := A) (n := cap);
      [ exact HART | exact INA | exact HT | unfold S_DRIVER; rewrite unsigned_lit by lia; cbn; tauto
      | rewrite !unsigned_lit by lia; lia | lia | exact ST | exact CEIL | unfold AMALLOC_STACK; lia
      | unfold AERRNO, ATP; exact ER | exact MI | exact TP | reflexivity | exact HB | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' g' TRS' MI' ST' ER' PR GM HT' HV HART'.
    replace (ret_pc (Z_to_bv 64 0x820b4)) with (Z_to_bv 64 0x820b4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (main_epilogue_exit AI SO_EXIT) with (lo := lo) (tid := tid) (code := code) (fj := fj) (v0 := v0) (v1 := v1) (v2 := v2) (v3 := v3) (v4 := v4) (v5 := v5) (v6 := v6) (v7 := v7);
      [ eapply DMOD_vm_only; [exact DM| exact HV] | left; reflexivity | reflexivity | exact CODE | exact TP
      | eapply cj_pres_rw_cells; [exact PR| exact FR| left; unfold mframe; cbn; lia] | exact ST' | exact CEIL
      | unfold AEXIT_DEPTH, AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH; lia | lia | exact HART'
      | eapply ADSTAT_cj_pres; [exact DS| exact PR] | exact TID
      | eapply stdout_file_cj_pres; [exact SOF| exact PR] | lia
      | apply stderr_wfile0_file; eapply stderr_wfile0_cj_pres; [exact SEF| exact PR]
      | eapply stdin_file_cj_pres; [exact SIF| exact PR] | exact MI' ].
  Qed.

  (* [comment removed for export] *)
  Lemma sxb_cases : forall b : byte,
    (bv_unsigned b < 128 /\ Z.land (bv_signed b) 18446744073709551615 = bv_unsigned b)
    \/ (128 <= bv_unsigned b /\ Z.land (bv_signed b) 18446744073709551615 = 2^64 - 256 + bv_unsigned b).
  Proof.
    intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
    change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
    unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
    destruct (Z_lt_dec (bv_unsigned b) 128).
    - left. split; [lia|]. rewrite (Z.mod_small (bv_unsigned b + 128)) by lia. rewrite Z.mod_small by lia. lia.
    - right. split; [lia|]. replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z.mod_add, (Z.mod_small (bv_unsigned b - 128)) by lia.
      replace (bv_unsigned b - 128 - 128) with ((2 ^ 64 - 256 + bv_unsigned b) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma main_tail : forall (A cap st : Z) (so : stdout_st) (b1 : byte) (ms0 ms2 ms3 ms4 : word) ms mo g,
    trun_ret AI TI sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 (wz ASTAGE2_RET) ms0 (wz A) ms2 ms3 ms4 (Z_to_bv 64 (bv_signed b1)) (wz ARS) (wz 0) q8 q9 q10 q11 A cap st so ms mo g ->
    0 <= st < 256 -> zlength (so_buf so) <= 8 ->
    LRZ asegs ms mo g (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (wz (if 128 <=? bv_unsigned b1 then 0 else st)) fs)).
  Proof.
    intros until g. intros RET ST8 SOB.
    (nelim RET 39%nat; intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' e' LB' TRS' B' np' -> FRM' MI' ST' ER' HART' INA HT' HB' FR DS DIC SEF SIF SSZ SOF DM).
    pose proof (bv_unsigned_in_range 8 b1) as R1. change (bv_modulus 8) with 256 in R1.
    unfold wz. apply lrz_step_evt.
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      destruct (sxb_cases b1) as [[B1 E]|[B1 E]]; rewrite E in K; [exfalso; lia|].
      replace (128 <=? bv_unsigned b1) with true by (symmetry; apply Z.leb_le; lia).
      do 6 step. if_true. apply evt_done.
      eapply main_free_exit; [exact HART'| exact INA| exact HT'| exact HB'| exact DM| lia| exact ER'| exact MI'| exact ST'| exact FR| exact DS| exact DIC| exact SOF| exact SOB| exact SEF| exact SIF| exact SSZ].
    - destruct (sxb_cases b1) as [[B1 E]|[B1 E]]; rewrite E in K; [| exfalso; lia].
      replace (128 <=? bv_unsigned b1) with false by (symmetry; apply Z.leb_gt; lia).
      do 2 step. apply evt_done.
      eapply main_free_exit; [exact HART'| exact INA| exact HT'| exact HB'| exact DM| lia| exact ER'| exact MI'| exact ST'| exact FR| exact DS| exact DIC| exact SOF| exact SOB| exact SEF| exact SIF| exact SSZ].
  Qed.

  (* [comment removed for export] *)
  Lemma main_fwrite_die : forall (msgA : Z) (msg : list byte) (SO : so_diag_lit_stmt msgA 31 msg)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost) (LB : list cblock) (TRS : list (list Z)) (B np A cap : Z) (e : word)
      (ra t0 t1 t2 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word),
    ART (bv_unsigned sp + 128) SPB LB [] TRS B m mo g -> In (A, cap) LB -> TINV TI np TRS -> cost_free <= B -> DMOD fs FDS0 mo ->
    rw_cells asegs m AERRNO [C4 e] -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> FRAME m ->
    ADSTAT tid m -> DICPT m -> stdout_file m stdout_init -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) (wz msgA) (wz 31) a2 (wz ASTDERR) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                  F (wz 0x820a4) fc None m (seg_rom asegs)) mo g
        (t_die msg fs).
  Proof.
    intros until t6. intros HART INA HT HB DM ER MI ST FR DS DIC SOF SEF SIF SSZ.
    destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    pose proof (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) as (IC & _).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART) as LOW.
    (nelim (ADSTAT_ssp tid m DS) 3%nat; intros cn0 SSP _).
    unfold wz. unfold AERRNO, ATP in ER.
    apply lrz_die. apply lrz_step_evt. do 2 step. apply evt_done.
    eapply (SO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g lo cn0);
      [ exact CH2 | exact SEF | exact IC | exact (DICPT_fwrite m DIC) | exact LOW | reflexivity | reflexivity | reflexivity | reflexivity
      | exact ST | exact CEIL | unfold AFWRITE_STACK; lia | exact SSP | exact MI | apply t_emit_has_nil' | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MU2 WM2 MI2 ST2 SEF2 SSP2.
    replace (ret_pc (Z_to_bv 64 0x820ac)) with (Z_to_bv 64 0x820ac : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (WOK : Forall (cj_write_ok (bv_unsigned sp + 128) SPB LB []) [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (ASTDERR, ASTDERR + 232)]).
    { apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit; unfold AFWRITE_STACK|]; lia|]. apply Forall_cons; [apply cj_write_ok_stderr| apply Forall_nil]. }
    assert (HART2 : ART (bv_unsigned sp + 128) SPB LB [] TRS B m2 mo g) by (eapply (art_frame AI); [exact HART| exact MU2| exact WM2| exact WOK]).
    unfold mframe in FR. axport ER MU2 WM2 ER2. axport FR MU2 WM2 FR2. axport DS MU2 WM2 DS2. axport DIC MU2 WM2 DIC2. axport SOF MU2 WM2 SOF2. axport SIF MU2 WM2 SIF2. axport SSZ MU2 WM2 SSZ2.
    change (W 1 []) with (W 1 (to_bytes (so_buf stdout_init))).
    eapply main_free_exit; [exact HART2| exact INA| exact HT| exact HB| exact DM| lia| unfold AERRNO, ATP; exact ER2| exact MI2| exact ST2| exact FR2| exact DS2| exact DIC2| exact SOF2
                           | unfold zlength; cbn [length so_buf stdout_init Z.of_nat]; lia| exact SEF2| exact SIF2| exact SSZ2].
  Qed.

  (* [comment removed for export] *)
  Lemma main_short : forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost) (LB : list cblock) (TRS : list (list Z)) (B np A cap : Z) (e : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word),
    ART (bv_unsigned sp + 128) SPB LB [] TRS B m mo g -> In (A, cap) LB -> TINV TI np TRS -> cost_free <= B -> DMOD fs FDS0 mo ->
    rw_cells asegs m AERRNO [C4 e] -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> FRAME m ->
    ADSTAT tid m -> DICPT m -> stdout_file m stdout_init -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                  F (wz 0x82070) fc None m (seg_rom asegs)) mo g
        (t_die msg_short fs).
  Proof.
    intros until t6. intros HART INA HT HB DM ER MI ST FR DS DIC SOF SEF SIF SSZ.
    (nelimp DS 18%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G1 G2 _).
    unfold wz, AGOT_STDERR, ASTDERR_VAR in G1, G2. revert G1 G2. exit_lits. intros G1 G2.
    unfold wz. apply lrz_step_evt. do 7 step. apply evt_done.
    apply (main_fwrite_die A_MSG_short msg_short SO_SHORT F fc m mo g LB TRS B np A cap e); assumption.
  Qed.

  Lemma main_overrun : forall (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost) (LB : list cblock) (TRS : list (list Z)) (B np A cap : Z) (e : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 t3 t4 t5 t6 : word),
    ART (bv_unsigned sp + 128) SPB LB [] TRS B m mo g -> In (A, cap) LB -> TINV TI np TRS -> cost_free <= B -> DMOD fs FDS0 mo ->
    rw_cells asegs m AERRNO [C4 e] -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> FRAME m ->
    ADSTAT tid m -> DICPT m -> stdout_file m stdout_init -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 q8 q9 q10 q11 t3 t4 t5 t6)
                  F (wz 0x8208c) fc None m (seg_rom asegs)) mo g
        (t_die msg_overrun fs).
  Proof.
    intros until t6. intros HART INA HT HB DM ER MI ST FR DS DIC SOF SEF SIF SSZ.
    (nelimp DS 18%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G1 G2 _).
    unfold wz, AGOT_STDERR, ASTDERR_VAR in G1, G2. revert G1 G2. exit_lits. intros G1 G2.
    unfold wz. apply lrz_step_evt. do 6 step. apply evt_done.
    apply (main_fwrite_die A_MSG_overrun msg_overrun SO_OVERRUN F fc m mo g LB TRS B np A cap e); assumption.
  Qed.

  (* [comment removed for export] *)
  Theorem post_ok : forall (F : bvmap 5 word) (fc : bv 32),
    frm0 fc -> post_stmt AI DI TI sp gp tp F fc fs lo SPB P1 tid (wz ASTAGE2_RET) path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
  Proof.
    intros F fc FRM. unfold post_stmt. intros cap A TRS B np junk m mo g ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 IV LT.
    destruct IV as (ST & MI & FR & DS & DIC & [e ER] & IFL & SOF & SEF & SIF & SSZ & BY & HART & HT & NP & HB & DM & FL & BLK & SOK & [stj RSC] & (k & CAP & HDRV) & LEN1 & LEN2 & CAP2).
    pose proof RSN_Z as HRSN. pose proof ARS_eq as HARS.
    pose proof DM as [MFDS HFS HH].
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(left; reflexivity)) as BR.
    (nelimp BR 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    assert (DRVB : DRV_B_TRUN = 515669262528) by (vm_compute; reflexivity).
    assert (QNN : 0 <= 2^26 / cap) by (apply Z.div_pos; lia).
    set (len := zlength data) in *.
    unfold wz in *. unfold AERRNO, ATP in ER. unfold AINITFLAG in IFL.
    (* [comment removed for export] *)
    apply lrz_step_evt. do 2 step. apply evt_done.
    eapply (lrz_impl_close asegs _ _ mo g 3 (FdFile path (Z_to_bv 64 len))); [| rewrite MFDS; reflexivity|].
    { eapply close_spec with (lo := lo) (errv := e);
        [ exact ST | change (errno_addr tp) with (bv_unsigned tp + -164); rewrite (errno_addr_tp tp TP); unfold AERRNO, ATP; exact ER | exact MI
        | reflexivity | lia | lia
        | change (errno_addr tp) with (bv_unsigned tp + -164); rewrite (errno_addr_tp tp TP); unfold AERRNO, ATP; lia
        | rewrite TP; unfold ATP; rewrite unsigned_lit by lia; lia ]. }
    cbv zeta. intros ms2 PO.
    (nelim PO 21%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2).
    cbn [close_ret close_errno] in *. change (errno_addr tp) with (bv_unsigned tp + -164) in MU2, ER2. rewrite (errno_addr_tp tp TP) in MU2, ER2.
    replace (ret_pc (Z_to_bv 64 0x81fb4)) with (Z_to_bv 64 0x81fb4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite MFDS, FDS3_remove.
    unfold mframe in FR. axport FR MU2 WM2 FR2. axport DS MU2 WM2 DS2. axport DIC MU2 WM2 DIC2. axport IFL MU2 WM2 IFL2. axport SOF MU2 WM2 SOF2. axport SEF MU2 WM2 SEF2.
    axport SIF MU2 WM2 SIF2. axport SSZ MU2 WM2 SSZ2. axport BLK MU2 WM2 BLK2.
    assert (WOK : Forall (cj_write_ok (bv_unsigned sp + 128) SPB [(A, cap)] []) [(bv_unsigned sp - 32, bv_unsigned sp); (AERRNO, AERRNO + 4)]).
    { apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit|]; lia|]. apply Forall_cons; [apply cj_write_ok_errno| apply Forall_nil]. }
    assert (HART2 : ART (bv_unsigned sp + 128) SPB [(A, cap)] [] TRS B m2 (with_fds FDS0 mo) g).
    { apply (art_model_frame AI _ _ _ _ _ _ m2 mo _ g); [| reflexivity| reflexivity| exact HH].
      eapply (art_frame AI); [exact HART| exact MU2| exact WM2| exact WOK]. }
    assert (HDRV2 : ADRV 1 m2 (with_fds FDS0 mo) g).
    { apply (adrv_weaken AI DI (loop_tokens k)); [| pose proof (Z.pow_le_mono_r 2 11 (Z.of_nat k) ltac:(lia)) as PW; unfold loop_tokens; destruct (Nat.le_gt_cases 11 k) as [K11|K11]; [exfalso; specialize (PW ltac:(lia)); change (2 ^ 11) with 2048 in PW; lia| lia]].
      apply (adrv_model AI DI _ m2 mo _ g); [| reflexivity| reflexivity| exact HH].
      eapply (adrv_frame AI DI); [exact HART| exact HDRV| exact MU2| exact WM2| exact WOK]. }
    assert (DM2 : DMOD fs FDS0 (with_fds FDS0 mo)) by (eapply DMOD_with_fds; exact DM).
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ A cap HART2 ltac:(left; reflexivity)) as [_ SOK0].
    assert (HB' : cost_free <= B) by (unfold loop_budget, cost_free in *; rewrite DRVB in HB; lia).
    clear FR DS DIC IFL SOF SEF SIF SSZ BLK HART HDRV MU2 WM2 ST MI ER.
    (* [comment removed for export] *)
    apply lrz_step_evt. do 2 step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    { apply evt_done.
      replace (t_body data fs) with (t_die msg_short fs).
      2:{ unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; subst len; unfold zlength in *; lia).
          replace (length data <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; subst len; unfold zlength in *; lia). reflexivity. }
      eapply main_short; [exact HART2| left; reflexivity| exact HT| exact HB'| exact DM2| unfold AERRNO, ATP; exact ER2| exact MI2| exact ST2| exact FR2| exact DS2| exact DIC2| exact SOF2| exact SEF2| exact SIF2| exact SSZ2]. }
    (* [comment removed for export] *)
    rewrite firstn_all2 in BLK2 by (subst len; unfold zlength in *; lia).
    pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ (proj1 (proj1 (rw_cells_app m2 A [CB (Z.to_nat len) data] _) BLK2)))) as BYA.
    destruct (nth_error data 0) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. subst len; unfold zlength in *; lia. }
    destruct (nth_error data 1) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. subst len; unfold zlength in *; lia. }
    pose proof (u8ro_read asegs m2 A data 0 b0 _ BYA Hb0 ltac:(lia) eq_refl) as RD0.
    pose proof (u8ro_read asegs m2 A data 1 b1 _ BYA Hb1 ltac:(lia) eq_refl) as RD1.
    replace (wa (A + 0)) with (wa A) in RD0 by (f_equal; lia).
    pose proof (bv_unsigned_in_range 8 b0) as Rb0. change (bv_modulus 8) with 256 in Rb0.
    pose proof (bv_unsigned_in_range 8 b1) as Rb1. change (bv_modulus 8) with 256 in Rb1.
    do 5 step. rewrite cfg_decode.
    set (cl := (bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768) in *.
    assert (Hcl : 0 <= cl < 32768) by (subst cl; apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    do 2 step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    { apply evt_done.
      replace (t_body data fs) with (t_die msg_overrun fs).
      2:{ unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; subst len; unfold zlength in *; lia).
          replace (length data <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; subst len; unfold zlength in *; lia).
          rewrite (nth_error_nth _ _ _ Hb0), (nth_error_nth _ _ _ Hb1). cbv zeta.
          replace (length data <? 6 + Z.to_nat ((bv_unsigned b0 + 256 * bv_unsigned b1) mod 32768))%nat with true
            by (symmetry; apply Nat.ltb_lt; subst len cl; unfold zlength in *; lia). reflexivity. }
      eapply main_overrun; [exact HART2| left; reflexivity| exact HT| exact HB'| exact DM2| unfold AERRNO, ATP; exact ER2| exact MI2| exact ST2| exact FR2| exact DS2| exact DIC2| exact SOF2| exact SEF2| exact SIF2| exact SSZ2]. }
    (* [comment removed for export] *)
    destruct (nth_error data (Z.to_nat (2 + cl + 0))) as [p0|] eqn:Hp0. 2:{ exfalso. apply nth_error_None in Hp0. subst len; unfold zlength in *; lia. }
    destruct (nth_error data (Z.to_nat (2 + cl + 1))) as [p1|] eqn:Hp1. 2:{ exfalso. apply nth_error_None in Hp1. subst len; unfold zlength in *; lia. }
    destruct (nth_error data (Z.to_nat (2 + cl + 2))) as [p2|] eqn:Hp2. 2:{ exfalso. apply nth_error_None in Hp2. subst len; unfold zlength in *; lia. }
    destruct (nth_error data (Z.to_nat (2 + cl + 3))) as [p3|] eqn:Hp3. 2:{ exfalso. apply nth_error_None in Hp3. subst len; unfold zlength in *; lia. }
    pose proof (u8ro_read asegs m2 A data (2 + cl + 0) p0 _ BYA Hp0 ltac:(lia) eq_refl) as RP0.
    pose proof (u8ro_read asegs m2 A data (2 + cl + 1) p1 _ BYA Hp1 ltac:(lia) eq_refl) as RP1.
    pose proof (u8ro_read asegs m2 A data (2 + cl + 2) p2 _ BYA Hp2 ltac:(lia) eq_refl) as RP2.
    pose proof (u8ro_read asegs m2 A data (2 + cl + 3) p3 _ BYA Hp3 ltac:(lia) eq_refl) as RP3.
    replace (wa (A + (2 + cl + 0))) with (wa (A + 2 + cl)) in RP0 by (f_equal; lia).
    replace (wa (A + (2 + cl + 1))) with (wa (A + 2 + cl + 1)) in RP1 by (f_equal; lia).
    replace (wa (A + (2 + cl + 2))) with (wa (A + 2 + cl + 2)) in RP2 by (f_equal; lia).
    replace (wa (A + (2 + cl + 3))) with (wa (A + 2 + cl + 3)) in RP3 by (f_equal; lia).
    do 6 step.
    do 16 step. apply evt_done.
    rewrite (unsigned_lit cl) by lia. rewrite (unsigned_lit len) by (subst len; unfold zlength in *; lia).
    replace (Z_to_bv 64 (A + 2 + cl + 4)) with (Z_to_bv 64 (A + 6 + cl)) by (f_equal; lia).
    replace (Z_to_bv 64 (len - cl + -6)) with (Z_to_bv 64 (len - 6 - cl)) by (f_equal; lia).
    replace (Z_to_bv 64 (len + - cl + -6)) with (Z_to_bv 64 (len - 6 - cl)) by (f_equal; lia).
    unfold sxb.
    clear RD0 RD1 RP0 RP1 RP2 RP3 Hp0 Hp1 Hp2 Hp3 BYA.
    (* [comment removed for export] *)
    rewrite (t_body_run data fs b0 b1 cl len Hb0 Hb1 eq_refl eq_refl ltac:(unfold MAX_INPUT; lia) ltac:(lia)).
    (nelim (tcalls_S cl data) 3%nat; intros j TC J3). rewrite TC.
    assert (SIDE : trun_side sp tp lo SPB).
    { split; [exact TP|]. split; [exact LO|]. split; [exact GT|]. split; [exact SPH|]. split; [exact SPBE|]. split; [exact SPAL|]. split; [exact WIN| exact BOT]. }
    eapply lrz_conseq.
    { eapply (TRUN sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 (Z_to_bv 64 ASTAGE2_RET) _ _ _ _ _ _ _ _ q8 q9 q10 q11 A cap SIDE
                    _ _ _ _ _ _ _ _ _ _ _ F fc m2 (with_fds FDS0 mo) g TRS B junk data cl e
                    (t_emit (W 1 (to_bytes (lines j))) (t_exit (Z_to_bv 64 0) fs)));
        [ exact HART2 | rewrite <- NP; exact HT | unfold loop_budget in HB; rewrite DRVB; lia | exact NPOK | exact HDRV2
        | exact BLK2 | exact SOK0 | lia | lia | unfold MAX_INPUT; lia | lia
        | exact DM2 | exact FRM | exact ST2 | exact MI2 | unfold AERRNO, ATP; exact ER2 | unfold AINITFLAG; exact IFL2 | exact DS2 | exact DIC2 | exact SOF2 | exact SEF2 | exact SIF2 | exact SSZ2 | exact FR2
        | apply t_emit_has_nil' | ].
      - (* [comment removed for export] *)
        intros ms' mo' g' RET. rewrite TC in RET. replace (S j - 1)%nat with j in RET by lia.
        replace (t_exit (Z_to_bv 64 0) fs) with (t_exit (wz (if 128 <=? bv_unsigned b1 then 0 else 0)) fs) by (destruct (128 <=? bv_unsigned b1); reflexivity).
        change (lines j) with (so_buf (so_after j)).
        eapply main_tail; [exact RET| lia| cbn [so_buf so_after]; rewrite lines_length; lia]. }
    (* [comment removed for export] *)
    cbv zeta. unfold exit_code. rewrite zero_lines_S. subst len. unfold W. rewrite map_app.
    apply t_eq_sym. apply t_emit_app'.
  Qed.
End S.

(* [comment removed for export] *)
Theorem post_proof (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface) :
  drv_traces_ok TI -> 4 * FUZZ_NP (2^26) <= NPMAX TI -> so_exit_stmt -> so_diag_short_stmt -> so_diag_overrun_stmt -> trun_all AI DI TI ->
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid : word)
         (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 : word),
    loop_side sp tp fc lo SPB P1 tid path slack ->
    post_stmt AI DI TI sp gp tp F fc fs lo SPB P1 tid (wz ASTAGE2_RET) path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
Proof.
  intros TROK NPOK SE SS SV TR. intros until q11. intros nelH_; (nelim nelH_ 15%nat; intros TP LO GT SPH SPBE TID FRM NONUL SLK LEN PUS PHI SPAL WIN BOT).
  eapply post_ok; eassumption.
Qed.

End CeilWrap.

End Drv_hdr.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_mem4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_icpt_read.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module Drv_loop.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.LRzAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_mem4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art Drv_exit Drv_die OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_xport OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_hooks.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma firstn_add_skipn : forall {X} (l : list X) n k, firstn (n + k) l = firstn n l ++ firstn k (skipn n l).
Proof.
  intros X l n. revert l. induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma firstn_app_read : forall {X} (data : list X) (len n want : nat),
  n = length (firstn want (skipn len data)) ->
  firstn len data ++ firstn want (skipn len data) = firstn (len + n) data.
Proof.
  intros X data len n want ->. rewrite firstn_add_skipn. f_equal.
  rewrite length_firstn. rewrite Nat.min_comm. symmetry.
  destruct (Nat.le_gt_cases want (length (skipn len data))).
  - rewrite Nat.min_r by lia. reflexivity.
  - rewrite Nat.min_l by lia. rewrite !firstn_all2 by lia. reflexivity.
Qed.

Lemma pow2_ge1 : forall k : nat, 1 <= 2 ^ Z.of_nat k.
Proof. intros k. pose proof (Z.pow_le_mono_r 2 0 (Z.of_nat k) ltac:(lia) ltac:(lia)) as H. change (2 ^ 0) with 1 in H. exact H. Qed.

(* [comment removed for export] *)
Lemma cap_k_lt : forall (cap : Z) (k : nat), cap = 65536 * 2 ^ Z.of_nat k -> cap < 2 ^ 26 -> (k < 10)%nat.
Proof.
  intros cap k -> LT. destruct (Nat.lt_ge_cases k 10) as [H|H]; [exact H|]. exfalso.
  pose proof (Z.pow_le_mono_r 2 10 (Z.of_nat k) ltac:(lia) ltac:(lia)). cbn in *. lia.
Qed.

(* [comment removed for export] *)
Lemma grow_cost : forall (cap : Z) (k : nat), cap = 65536 * 2 ^ Z.of_nat k -> cap < 2 ^ 26 ->
  (cost_malloc (cap * 2) + cost_free <= 9 * cap + 2^19 /\ 64512 < cap * 2 < 2 ^ 32)
  /\ (2^26 / cap = 2 * (2^26 / (cap * 2)) /\ 1 <= 2^26 / (cap * 2)).
Proof.
  intros cap k E LT. pose proof (cap_k_lt cap k E LT) as K. subst cap.
  do 10 (destruct k as [|k]; [vm_compute; split; [split; [discriminate| split; reflexivity]| split; [reflexivity| discriminate]] |]). lia.
Qed.

Lemma cap_next : forall (cap : Z) (k : nat), cap = 65536 * 2 ^ Z.of_nat k -> cap < 2 ^ 26 -> cap * 2 <= 2 ^ 26 /\ cap * 2 = 65536 * 2 ^ Z.of_nat (S k).
Proof.
  intros cap k -> LT. split.
  - destruct (Z_lt_dec (Z.of_nat k) 10).
    + pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 9 ltac:(lia) ltac:(lia)). cbn in *. lia.
    + pose proof (Z.pow_le_mono_r 2 10 (Z.of_nat k) ltac:(lia) ltac:(lia)). cbn in *. lia.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Section S.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface).
  Let ART := CJ_iface.ART AI.
  Let ADRV := Drv_iface2.ADRV AI DI.
  Hypothesis TROK : drv_traces_ok TI.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_REFUSED : so_diag_refused_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.

  Lemma cj_pres_bytes_at_hi : forall sp0 LB LF SP m m' A bs,
    cj_pres sp0 LB LF SP m m' -> bytes_at asegs m A bs -> SP <= A -> A + Z.of_nat (length bs) <= 2^47 -> bytes_at asegs m' A bs.
  Proof.
    intros sp0 LB LF SP m m' A bs HP (H0 & H1 & HB) HS HH. split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply argv_client; lia)) as [E _]. rewrite E. reflexivity.
  Qed.

  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
            (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 : word) (q8 q9 q10 q11 : word).
  Hypothesis TP : tp = wz ATP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 2^47.
  Hypothesis SPBE : SPB = bv_unsigned sp + 80.
  Hypothesis TID : 0 < bv_unsigned tid < 2^22.
  Hypothesis FRM : frm0 fc.
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) path.
  Hypothesis SLK : (- (P1 + zlength path + 1)) mod 8 <= zlength slack.
  Hypothesis LEN : zlength path <= 131071.
  Hypothesis PUS : bv_unsigned sp + 128 <= P1.
  Hypothesis PHI : P1 + zlength path + 1 + zlength slack + 16 <= 2^47.

  Notation INV := (loop_inv AI DI TI sp fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7).
  Notation REGS := (loop_regs sp gp tp F fc P1 q8 q9 q10 q11).

  (* [comment removed for export] *)
  Definition HEAD_OK (bound : Z) : Prop :=
    forall len cap A TRS B np junk m mo g ms,
      INV len cap A TRS B np junk m mo g -> len < cap -> REGS len cap A m 0x81f84 ms -> zlength data - len < bound ->
      LRZ asegs ms mo g (Kloop data fs cap).

  Hypothesis POST : post_stmt AI DI TI sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.

  Lemma head_ok_mono : forall b b', HEAD_OK b -> b' <= b -> HEAD_OK b'.
  Proof. intros b b' H LE len cap A TRS B np junk m mo g ms IV LT RG LT'. apply (H len cap A TRS B np junk m mo g ms IV LT RG). lia. Qed.

  (* [comment removed for export] *)
  Lemma loop_grow : forall (cap A : Z) TRS B np junk m mo g (b : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      INV cap cap A TRS B np junk m mo g -> HEAD_OK b -> zlength data - cap < b ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz cap) (wz 3) (wz cap) (wz ARS) (wz A) q8 q9 q10 q11 t3 t4 t5 t6)
                    F (wz 0x81f4c) fc None m (seg_rom asegs)) mo g
          (Kloop data fs cap).
  Proof.
    intros until t6. intros IV IH IHb.
    destruct IV as (ST & MI & FR & DS & DIC & [e ER] & IFL & SOF & SEF & SIF & SSZ & BY & HART & HT & NP & HB & DM & FL & BLK & SOK & [stj RSC] & (k & CAP & HDRV) & LEN1 & LEN2 & CAP2).
    pose proof RSN_Z as HRSN. pose proof ARS_eq as HARS.
    pose proof DM as [MFDS HFS HH].
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(left; reflexivity)) as BR.
    (nelimp BR 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    pose proof (ablk_disj_band _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(left; reflexivity))) as BDJ. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in BDJ.
    pose proof (pow2_ge1 k) as K2.
    unfold wz in *. unfold AERRNO, ATP in ER. unfold AINITFLAG in IFL.
    apply lrz_step_evt.
    do 2 step. if_cases K; zify_cond K; rewrite Z.shiftr_div_pow2 in K by lia.
    - (* [comment removed for export] *)
      assert (CAPB : 2 ^ 26 <= cap) by (apply Z.nlt_ge; intros Hlt; apply K; apply Z.div_small; lia).
      apply evt_done.
      replace (Kloop data fs cap) with (t_die msg_refused fs).
      2:{ unfold Kloop.
          unfold t_body. replace (MAX_INPUT <=? Z.of_nat (length data)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT, zlength in *; lia). reflexivity. }
      eapply (die_refused AI SO_EXIT SO_REFUSED) with (lo := lo) (tid := tid) (sp0 := bv_unsigned sp + 128) (SPB := SPB) (LB := [(A, cap)]) (TRS := TRS) (B := B);
        [ exact DM | right; eexists; reflexivity | exact TP | exact CEIL | lia | lia | lia | exact TID | exact FRM | ].
      split; [exact ST|]. split; [exact MI|]. split; [exact DS|]. split; [exact DIC|]. split; [exact SOF|]. split; [exact SEF|].
      split; [exact SIF|]. split; [exact SSZ| exact HART].
    - (* [comment removed for export] *)
      assert (CAPB : cap < 2 ^ 26) by (destruct (Z_lt_dec cap (2 ^ 26)) as [Hl|Hl]; [exact Hl|]; exfalso; pose proof (Z.div_str_pos cap (2 ^ 26) ltac:(lia)); lia).
      destruct (cap_next cap k CAP CAPB) as [CAP2' CAPS]. destruct (grow_cost cap k CAP CAPB) as [[COST SEC] [QD QP]].
      pose proof (cap_k_lt cap k CAP CAPB) as KLT.
      assert (DRVB : DRV_B_TRUN = 515669262528) by (vm_compute; reflexivity). unfold loop_budget in HB. rewrite DRVB in HB. unfold cost_free in COST.
      do 3 step. apply evt_done.
      rewrite (unsigned_lit cap) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      (* [comment removed for export] *)
      change (Kloop data fs cap) with (Kloop data fs (cap * 2)).
      assert (HDRVS : ADRV (S (loop_tokens (S k))) m mo g).
      { replace (S (loop_tokens (S k))) with (loop_tokens k) by (unfold loop_tokens; lia). exact HDRV. }
      eapply (drv_malloc_nn AI TI TROK DI (loop_tokens (S k))) with (lo := lo) (np := np) (n := cap * 2);
        [ exact HART | exact HDRVS | exact HT | unfold S_DRIVER; rewrite unsigned_lit by lia; cbn; tauto
        | rewrite !unsigned_lit by lia; lia | lia | exact ST | exact CEIL | unfold AMALLOC_STACK; lia
        | unfold AERRNO, ATP; exact ER | exact MI | exact TP | reflexivity | unfold DRV_REQ_MAX; lia
        | lia | unfold DRV_BFLOOR; lia | intros EP; exfalso; pose proof (is_primary_bound (cap * 2) ltac:(lia) EP); lia | ].
      (* [comment removed for export] *)
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 g2 errv2 TRS2 A' junk' MI2 ST2 ER2 PR GM HT2 HV NZ BR' NIN HA2 HD2 BLK'.
      pose proof (DMOD_vm_only _ _ _ _ DM HV) as DM2.
      replace (ret_pc (Z_to_bv 64 0x81f60)) with (Z_to_bv 64 0x81f60 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (nelimp BR' 4%nat; intros BQ1 BQ2 BQ3 BQ4). unfold AIMG_HI in BQ1.
      (* [comment removed for export] *)
      pose proof (ablk_disj_band _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ A' (cap * 2) HA2 ltac:(left; reflexivity))) as BDJ'. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in BDJ'.
      cbn [map fst] in NIN. assert (NE : A' <> A) by (intros E; apply NIN; left; symmetry; exact E). clear NIN.
      pose proof (artcells_split m2 (art_rtcells AI _ _ _ _ _ _ _ _ _ HA2)) as (IC2 & _).
      (* [comment removed for export] *)
      assert (BLKo : rw_cells asegs m2 A [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)]).
      { pose proof (proj1 (proj1 (rw_cells_app m A [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)] _) BLK)) as B1.
        eapply cj_pres_rw_cells; [exact PR| exact B1| do 3 right; left; exists A, cap; split; [left; reflexivity| cbn; lia]]. }
      pose proof BLK' as BLKn.
      eapply (rw_cells_split_CB asegs m2 A' [] (Z.to_nat (cap * 2)) junk' [] [Z.to_nat cap; Z.to_nat cap]) in BLKn; [| cbn; lia]. cbn [mk_CB_cells app] in BLKn.
      pose proof (proj1 (rw_cells_app m2 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk')] _) BLKn) as [BLKn1 BLKn2].
      replace (A' + Z.of_nat (cells_size [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk')])) with (A' + cap) in BLKn2 by (cbn; lia). clear BLKn.
      pose proof (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ A' (cap * 2) A cap HA2 ltac:(left; reflexivity) ltac:(right; left; reflexivity) NE) as DISJ.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ A' (cap * 2) HA2 ltac:(left; reflexivity)) as [_ SOKn].
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ A cap HA2 ltac:(right; left; reflexivity)) as [_ SOKo].
      pose proof (art_block_app_range AI _ _ _ _ _ _ _ _ _ A' (cap * 2) A' cap HA2 ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as ARn.
      pose proof (art_block_app_range AI _ _ _ _ _ _ _ _ _ A cap A cap HA2 ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as ARo.
      (* [comment removed for export] *)
      apply lrz_step_evt. unfold wz.
      step. if_cases K'; zify_cond K'; [exfalso; lia|]. clear K'.
      step. step. if_cases K'; zify_cond K'; [exfalso; lia|]. clear K'.
      do 4 step.
      assert (LSRC : length (firstn (Z.to_nat cap) data) = Z.to_nat cap) by (rewrite length_firstn; unfold zlength in *; lia).
      eapply evt_cut.
      { eapply (memcpy_icpt_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 A' A cap (firstn (Z.to_nat cap) data) (firstn (Z.to_nat cap) junk') lo);
          rewrite ?unsigned_lit by lia;
          [ exact IC2 | exact MI2 | exact ST2 | exact CEIL | unfold AINTRIN_STACK; lia | reflexivity | reflexivity | reflexivity
          | exact (proj1 (rw_cells_CB_bytes _ _ _ _ BLKo)) | rewrite LSRC; lia | exact BLKn1 | (lia_on DISJ) | lia
          | exact ARo | exact ARn
          | apply wr_range_ok_high; lia
          | intros _; exact SOKo | intros _; eapply shadow_ok_sub; [exact SOKn| lia| lia| lia] | lia | lia ]. }
      intros ms3 nelH_; (nelim nelH_ 22%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MU3 WM3 MI3 DST3 SRC3 ST3).
      replace (ret_pc (Z_to_bv 64 0x81f7c)) with (Z_to_bv 64 0x81f7c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold zlength in *. rewrite ?(Z2Nat.id cap) in MU3, DST3 by lia.
      (* [comment removed for export] *)
      axport ER2 MU3 WM3 ER3. axport BLKn2 MU3 WM3 BLKn3.
      assert (WOK3 : Forall (cj_write_ok (bv_unsigned sp + 128) SPB [(A', cap * 2); (A, cap)] []) [(A', A' + cap); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]).
      { apply Forall_cons; [apply (cj_write_ok_block _ _ _ _ A' (cap * 2)); [left; reflexivity| lia| lia]|].
        apply Forall_cons; [apply cj_write_ok_stack; [unfold AINTRIN_STACK|]; lia| apply Forall_nil]. }
      assert (HA3 : ART (bv_unsigned sp + 128) SPB [(A', cap * 2); (A, cap)] [] TRS2 (B - cost_malloc (cap * 2)) m3 mo2 g2)
        by (eapply (art_frame AI); [exact HA2| exact MU3| exact WM3| exact WOK3]).
      assert (HD3 : ADRV (loop_tokens (S k)) m3 mo2 g2) by (eapply (adrv_frame AI DI); [exact HA2| exact HD2| exact MU3| exact WM3| exact WOK3]).
      (* [comment removed for export] *)
      do 2 step. apply evt_done.
      eapply (drv_free2 AI TI TROK DI (loop_tokens (S k))) with (lo := lo) (np := np) (A := A) (n := cap);
        [ exact HA3 | exact HD3 | right; left; reflexivity | exact HT2 | unfold S_DRIVER; rewrite unsigned_lit by lia; cbn; (cut_on [TID LEN1 BDJ SEC BDJ' DISJ] tauto)
        | rewrite !unsigned_lit by lia; lia | lia | exact ST3 | exact CEIL | unfold AMALLOC_STACK; lia
        | unfold AERRNO, ATP; exact ER3 | exact MI3 | exact TP | reflexivity | unfold cost_free; lia | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 mo4 g4 TRS4 MI4 ST4 ER4 PR4 GM4 HT4 HV4 HA4 HD4.
      replace (ret_pc (Z_to_bv 64 0x81f84)) with (Z_to_bv 64 0x81f84 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      cbn [cb_remove Z.eqb] in PR4, HA4. rewrite (proj2 (Z.eqb_neq A' A) NE) in PR4, HA4. rewrite Z.eqb_refl in PR4, HA4.
      (* [comment removed for export] *)
      assert (FR4 : rw_cells asegs m4 (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)).
      { assert (FR2 : rw_cells asegs m2 (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0))
          by (eapply cj_pres_rw_cells; [exact PR| exact FR| left; unfold mframe; cbn; lia]).
        unfold mframe in FR2. axport FR2 MU3 WM3 FR3. eapply cj_pres_rw_cells; [exact PR4| exact FR3| left; cbn; lia]. }
      assert (RSC4 : rw_cells asegs m4 ARS [CB RSN stj]).
      { assert (RSC2 : rw_cells asegs m2 ARS [CB RSN stj])
          by (eapply cj_pres_rw_cells; [exact PR| exact RSC| apply cj_client_range_img; unfold ARS, ADATA_LO, AIMG_HI, AERRNO, ATP; cbn; lia]).
        axport RSC2 MU3 WM3 RSC3.
        eapply cj_pres_rw_cells; [exact PR4| exact RSC3| apply cj_client_range_img; unfold ARS, ADATA_LO, AIMG_HI, AERRNO, ATP; cbn; lia]. }
      assert (DS4 : ADSTAT tid m4).
      { pose proof (ADSTAT_cj_pres _ _ _ _ _ _ _ DS PR) as DS2. axport DS2 MU3 WM3 DS3. eapply ADSTAT_cj_pres; [exact DS3| exact PR4]. }
      assert (DIC4 : DICPT m4).
      { pose proof (DICPT_cj_pres _ _ _ _ _ _ DIC PR) as DIC2. axport DIC2 MU3 WM3 DIC3. eapply DICPT_cj_pres; [exact DIC3| exact PR4]. }
      assert (IFL4 : rw_cells asegs m4 AINITFLAG [C1 (Z_to_bv 8 0)]).
      { assert (IFL2 : rw_cells asegs m2 AINITFLAG [C1 (Z_to_bv 8 0)])
          by (eapply cj_pres_rw_cells; [exact PR| exact IFL| apply cj_client_range_img; unfold AINITFLAG, ADATA_LO, AIMG_HI, AERRNO, ATP; cbn; lia]).
        axport IFL2 MU3 WM3 IFL3.
        eapply cj_pres_rw_cells; [exact PR4| exact IFL3| apply cj_client_range_img; unfold AINITFLAG, ADATA_LO, AIMG_HI, AERRNO, ATP; cbn; lia]. }
      assert (SOF4 : stdout_file m4 stdout_init).
      { pose proof (stdout_file_cj_pres _ _ _ _ _ _ _ SOF PR) as SOF2. axport SOF2 MU3 WM3 SOF3. eapply stdout_file_cj_pres; [exact SOF3| exact PR4]. }
      assert (SEF4 : stderr_wfile0 m4).
      { pose proof (stderr_wfile0_cj_pres _ _ _ _ _ _ SEF PR) as SEF2. axport SEF2 MU3 WM3 SEF3. eapply stderr_wfile0_cj_pres; [exact SEF3| exact PR4]. }
      assert (SIF4 : stdin_file m4).
      { pose proof (stdin_file_cj_pres _ _ _ _ _ _ SIF PR) as SIF2. axport SIF2 MU3 WM3 SIF3. eapply stdin_file_cj_pres; [exact SIF3| exact PR4]. }
      assert (SSZ4 : stack_shadow_zero m4).
      { pose proof (stack_shadow_zero_cj_pres _ _ _ _ _ _ SSZ PR (art_lowshadow AI _ _ _ _ _ _ _ _ _ HA2)) as SSZ2. sepM. axport SSZ2 MU3 WM3 SSZ3.
        eapply stack_shadow_zero_cj_pres; [exact SSZ3| exact PR4| exact (art_lowshadow AI _ _ _ _ _ _ _ _ _ HA4)]. }
      assert (BY4 : bytes_at asegs m4 P1 (path ++ Z_to_bv 8 0 :: slack)).
      { pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
        pose proof (cj_pres_bytes_at_hi _ _ _ _ _ _ _ _ PR BY ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia)) as BY2. axport BY2 MU3 WM3 BY3.
        eapply cj_pres_bytes_at_hi; [exact PR4| exact BY3| lia| rewrite length_app; cbn [length]; lia]. }
      assert (BLK4 : rw_cells asegs m4 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data); CB (Z.to_nat (cap * 2 - cap)) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk'))]).
      { eapply cj_pres_rw_cells; [exact PR4| | do 3 right; left; exists A', (cap * 2); split; [left; reflexivity| cbn; lia]].
        apply (proj2 (rw_cells_app m3 A' [CB (Z.to_nat cap) (firstn (Z.to_nat cap) data)] _)). split; [exact DST3|].
        cbn [cells_size Cells.csize Nat.add]. replace (A' + Z.of_nat (Z.to_nat cap + 0)) with (A' + cap) by lia.
        replace (Z.to_nat (cap * 2 - cap)) with (Z.to_nat cap) by lia. exact BLKn3. }
      assert (DM4 : DMOD fs (FDS3 (FdFile path (Z_to_bv 64 cap))) mo4).
      { eapply DMOD_vm_only; [| exact HV4]. exact DM2. }
      assert (SOK4 : shadow_ok m4 A' (cap * 2)) by (exact (proj2 (art_shadow AI _ _ _ _ _ _ _ _ _ A' (cap * 2) HA4 ltac:(left; reflexivity)))).
      assert (IV4 : INV cap (cap * 2) A' TRS4 (B - cost_malloc (cap * 2) - cost_free) np (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk')) m4 mo4 g4).
      { split; [exact ST4|]. split; [exact MI4|]. split; [exact FR4|]. split; [exact DS4|]. split; [exact DIC4|]. split; [exists errv2; exact ER4|]. split; [exact IFL4|].
        split; [exact SOF4|]. split; [exact SEF4|]. split; [exact SIF4|]. split; [exact SSZ4|]. split; [exact BY4|]. split; [exact HA4|]. split; [exact HT4|].
        split; [exact NP|]. split; [unfold loop_budget, cost_free; rewrite DRVB; lia|].
        split; [exact DM4|]. split; [exact FL|]. split; [exact BLK4|]. split; [exact SOK4|]. split; [exists stj; exact RSC4|].
        split; [exists (S k); split; [exact CAPS| exact HD4]|]. unfold zlength in *. lia. }
      clear FR4 DS4 DIC4 IFL4 SOF4 SEF4 SIF4 SSZ4 BY4 BLK4 RSC4 HA3 PR4 PR.
      (* [comment removed for export] *)
      eapply (IH cap (cap * 2) A' TRS4 _ np _ m4 mo4 g4 _ IV4); [lia| | unfold zlength in *; lia].
      unfold loop_regs. unfold wz. nexists 17%nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_read : forall (len cap A : Z) TRS B np junk m mo g (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (want : Z),
      INV len cap A TRS B np junk m mo g -> HEAD_OK (zlength data - len) ->
      len < cap -> want = Z.min (cap - len) 65536 ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 (wz want) a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz ARS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
                    F (wz 0x81f94) fc None m (seg_rom asegs)) mo g
          (Kloop data fs cap).
  Proof.
    intros until want. intros IV IH LT WANT.
    destruct IV as (ST & MI & FR & DS & DIC & [e ER] & IFL & SOF & SEF & SIF & SSZ & BY & HART & HT & NP & HB & DM & FL & BLK & SOK & [stj RSC] & (k & CAP & HDRV) & LEN1 & LEN2 & CAP2).
    pose proof RSN_Z as HRSN. pose proof ARS_eq as HARS.
    pose proof DM as [MFDS HFS HH].
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(left; reflexivity)) as BR.
    (nelimp BR 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    pose proof (ablk_disj_band _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(left; reflexivity))) as BDJ. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in BDJ.
    pose proof (pow2_ge1 k) as K2.
    pose proof (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) as (IC & _).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART) as LOW.
    unfold wz in *. unfold AERRNO, ATP in ER. unfold AINITFLAG in IFL.
    (* [comment removed for export] *)
    assert (RSCs : rw_cells asegs m ARS [CB (Z.to_nat want) (firstn (Z.to_nat want) stj); CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))]).
    { eapply (rw_cells_split_CB asegs m ARS [] RSN stj [] [Z.to_nat want; Z.to_nat (65536 - want)]) in RSC; [| pose proof RSN_Z; cbn [sum_nat]; lia].
      cbn [mk_CB_cells app] in RSC. exact RSC. }
    pose proof (proj1 (rw_cells_app m ARS [CB (Z.to_nat want) (firstn (Z.to_nat want) stj)] _) RSCs) as [RSCa RSCb].
    replace (ARS + Z.of_nat (cells_size [CB (Z.to_nat want) (firstn (Z.to_nat want) stj)])) with (ARS + want) in RSCb by (pose proof RSN_Z; cbn; lia).
    clear RSCs.
    apply lrz_step_evt.
    do 3 step. apply evt_done.
    eapply (lrz_impl_read_file asegs _ _ mo g 3 (bv_unsigned (Z_to_bv 64 ARS)) want path (Z_to_bv 64 len) data);
      [| rewrite MFDS; reflexivity| rewrite HFS; exact FL| rewrite rw_bytes_max_val; lia| rewrite unsigned_lit by lia; rewrite TASK_SIZE_val; unfold ARS; lia|].
    { eapply read_icpt_ok with (lo := lo) (junk := firstn (Z.to_nat want) stj) (errv := e);
        [ exact IC | exact (proj1 DIC) | exact MI | exact ST | exact CEIL | unfold AREAD_STACK; lia
        | rewrite unsigned_lit by lia; exact RSCa
        | change (errno_addr tp) with (bv_unsigned tp + -164); rewrite (errno_addr_tp tp TP); unfold AERRNO, ATP; exact ER
        | reflexivity | reflexivity | exact TP | lia | lia
        | rewrite unsigned_lit by lia; unfold stage_range, RS_LO, RS_HI; lia
        | rewrite unsigned_lit by lia; apply (lowsh_rs_shadow_ok m ARS want LOW); lia
        | rewrite unsigned_lit by lia; lia ]. }
    cbv zeta. intros ms2 PO.
    (nelim PO 23%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 RSC2 ER2 Hn).
    cbn [read_ret] in *. change (errno_addr tp) with (bv_unsigned tp + -164) in MU2, ER2. rewrite (errno_addr_tp tp TP) in MU2, ER2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in RSC2 by lia. rewrite (Z2Nat.id want) in MU2 by lia.
    set (bs := file_read data (Z_to_bv 64 len) (Z_to_bv 64 want)) in *.
    replace (ret_pc (Z_to_bv 64 0x81fa0)) with (Z_to_bv 64 0x81fa0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite MFDS, FDS3_insert.
    assert (LBS : Z.of_nat (length bs) = Z.min want (zlength data - len)).
    { subst bs. rewrite length_file_read. unfold word_to_nat. unfold zlength in *. rewrite !unsigned_lit by lia. (lia_on CAP LEN1 LEN2 LT WANT BR1). }
    set (n := Z.of_nat (length bs)) in *.
    assert (Hn' : 0 <= n <= want) by lia.
    assert (BS : firstn (Z.to_nat len) data ++ bs = firstn (Z.to_nat (len + n)) data).
    { subst bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia.
      replace (Z.to_nat (len + n)) with (Z.to_nat len + Z.to_nat n)%nat by (lia_on CAP LEN1 LT WANT BR1 Hn LBS). apply firstn_app_read.
      subst n. rewrite Nat2Z.id. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    unfold mframe in FR.
    axport FR MU2 WM2 FR2. axport DS MU2 WM2 DS2. axport DIC MU2 WM2 DIC2. axport IFL MU2 WM2 IFL2. axport SOF MU2 WM2 SOF2.
    axport SEF MU2 WM2 SEF2. axport SIF MU2 WM2 SIF2. axport SSZ MU2 WM2 SSZ2. axport BY MU2 WM2 BY2.
    axport BLK MU2 WM2 BLK2. axport RSCb MU2 WM2 RSCb2.
    assert (WOK : Forall (cj_write_ok (bv_unsigned sp + 128) SPB [(A, cap)] []) [(bv_unsigned sp - AREAD_STACK, bv_unsigned sp); (ARS, ARS + want); (AERRNO, AERRNO + 4)]).
    { apply Forall_cons; [apply cj_write_ok_stack; [unfold AREAD_STACK|]; lia|].
      apply Forall_cons; [apply cj_write_ok_img; unfold ADATA_LO, AIMG_HI; cbn [fst snd]; (lia_on HARS BR1 LEN1 WANT)|].
      apply Forall_cons; [apply cj_write_ok_errno| apply Forall_nil]. }
    assert (HART2 : ART (bv_unsigned sp + 128) SPB [(A, cap)] [] TRS B m2 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo) g).
    { apply (art_model_frame AI _ _ _ _ _ _ m2 mo _ g); [| reflexivity| reflexivity| exact HH].
      eapply (art_frame AI); [exact HART| exact MU2| exact WM2| exact WOK]. }
    assert (HDRV2 : ADRV (loop_tokens k) m2 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo) g).
    { apply (adrv_model AI DI _ m2 mo _ g); [| reflexivity| reflexivity| exact HH].
      eapply (adrv_frame AI DI); [exact HART| exact HDRV| exact MU2| exact WM2| exact WOK]. }
    assert (SOK2 : shadow_ok m2 A cap) by (exact (proj2 (art_shadow AI _ _ _ _ _ _ _ _ _ A cap HART2 ltac:(left; reflexivity)))).
    assert (DM2 : DMOD fs (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo)).
    { eapply DMOD_with_fds. exact DM. }
    pose proof (artcells_split m2 (art_rtcells AI _ _ _ _ _ _ _ _ _ HART2)) as (IC2 & _).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART2) as LOW2.
    (* [comment removed for export] *)
    apply lrz_step_evt.
    step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 2 step.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (NPOS : 0 < n) by (rewrite ?unsigned_lit in K by lia; lia). clear K.
      (* [comment removed for export] *)
      pose proof BLK2 as BLK0.
      eapply (rw_cells_split_CB asegs m2 A [CB (Z.to_nat len) (firstn (Z.to_nat len) data)] (Z.to_nat (cap - len)) junk [] [Z.to_nat n; Z.to_nat (cap - len - n)]) in BLK2; [| cbn; lia].
      cbn [mk_CB_cells app] in BLK2.
      pose proof (proj1 (rw_cells_app m2 A [CB (Z.to_nat len) (firstn (Z.to_nat len) data)] _) BLK2) as [BLKa BLKbc].
      pose proof (proj1 (rw_cells_app m2 _ [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)] _) BLKbc) as [BLKb BLKc].
      replace (A + Z.of_nat (cells_size [CB (Z.to_nat len) (firstn (Z.to_nat len) data)])) with (A + len) in BLKb, BLKc by (cbn; lia).
      replace (A + len + Z.of_nat (cells_size [CB (Z.to_nat n) (firstn (Z.to_nat n) junk)])) with (A + len + n) in BLKc by (cbn; lia).
      clear BLK2 BLKbc.
      (* [comment removed for export] *)
      pose proof (proj1 (rw_cells_app m2 ARS [CB (length bs) bs] _) RSC2) as [RSC2a RSC2b].
      replace (ARS + Z.of_nat (cells_size [CB (length bs) bs])) with (ARS + n) in RSC2b by (pose proof RSN_Z; cbn; lia).
      pose proof (art_block_app_range AI _ _ _ _ _ _ _ _ _ A cap (A + len) n HART2 ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as ARd.
      do 4 step.   (* [comment removed for export] *)
      eapply evt_cut.
      { eapply (memcpy_icpt_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (A + len) ARS n bs (firstn (Z.to_nat n) junk) lo);
          rewrite ?unsigned_lit by lia;
          [ exact IC2 | exact MI2 | exact ST2 | exact CEIL | unfold AINTRIN_STACK; lia | reflexivity | reflexivity | reflexivity
          | exact (proj1 (rw_cells_CB_bytes _ _ _ _ RSC2a)) | lia | exact BLKb | lia | lia
          | left; unfold lowmem_range, KLOWSHADOW_BEG; lia | exact ARd
          | apply wr_range_ok_high; lia
          | intros _; apply (lowsh_rs_shadow_ok m2 ARS n LOW2); lia | intros _; eapply shadow_ok_sub; [exact SOK2| lia| lia| lia] | lia | lia ]. }
      intros ms3 nelH_; (nelim nelH_ 22%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MU3 WM3 MI3 DST3 SRC3 ST3).
      replace (ret_pc (Z_to_bv 64 0x81f38)) with (Z_to_bv 64 0x81f38 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      axport FR2 MU3 WM3 FR3. sepM. axport DS2 MU3 WM3 DS3. axport DIC2 MU3 WM3 DIC3. axport IFL2 MU3 WM3 IFL3. axport SOF2 MU3 WM3 SOF3.
      axport SEF2 MU3 WM3 SEF3. axport SIF2 MU3 WM3 SIF3. axport SSZ2 MU3 WM3 SSZ3.
      axport BY2 MU3 WM3 BY3. axport ER2 MU3 WM3 ER3. axport BLKa MU3 WM3 BLKa3. axport BLKc MU3 WM3 BLKc3.
      axport RSC2b MU3 WM3 RSC2b3. axport RSCb2 MU3 WM3 RSCb3.
      pose proof (rw_cells_transport _ _ _ _ _ _ RSC2a MU3 WM3 ltac:(cbn; unfold AINTRIN_STACK; lia)) as RSC2a3.
      assert (WOK3 : Forall (cj_write_ok (bv_unsigned sp + 128) SPB [(A, cap)] []) [(A + len, A + len + n); (bv_unsigned sp - AINTRIN_STACK, bv_unsigned sp)]).
      { apply Forall_cons; [apply (cj_write_ok_block _ _ _ _ A cap); [left; reflexivity| lia| lia]|].
        apply Forall_cons; [apply cj_write_ok_stack; [unfold AINTRIN_STACK|]; lia| apply Forall_nil]. }
      assert (HART3 : ART (bv_unsigned sp + 128) SPB [(A, cap)] [] TRS B m3 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo) g)
        by (eapply (art_frame AI); [exact HART2| exact MU3| exact WM3| exact WOK3]).
      assert (HDRV3 : ADRV (loop_tokens k) m3 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo) g)
        by (eapply (adrv_frame AI DI); [exact HART2| exact HDRV2| exact MU3| exact WM3| exact WOK3]).
      assert (SOK3 : shadow_ok m3 A cap) by (exact (proj2 (art_shadow AI _ _ _ _ _ _ _ _ _ A cap HART3 ltac:(left; reflexivity)))).
      (* [comment removed for export] *)
      assert (BLK3 : rw_cells asegs m3 A [CB (Z.to_nat (len + n)) (firstn (Z.to_nat (len + n)) data); CB (Z.to_nat (cap - (len + n))) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))]).
      { assert (J1 : rw_cells asegs m3 A ([CB (Z.to_nat len) (firstn (Z.to_nat len) data)] ++ ([CB (length bs) bs] ++ [CB (Z.to_nat (cap - len - n)) (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk))]))).
        { apply (proj2 (rw_cells_app _ _ _ _)). split; [exact BLKa3|]. cbn [cells_size Cells.csize Nat.add].
          replace (A + Z.of_nat (Z.to_nat len + 0)) with (A + len) by lia.
          apply (proj2 (rw_cells_app _ _ _ _)). split.
          - replace (length bs) with (Z.to_nat n) by lia. exact DST3.
          - cbn [cells_size Cells.csize Nat.add]. replace (A + len + Z.of_nat (length bs + 0)) with (A + len + n) by lia. exact BLKc3. }
        cbn [app] in J1.
        pose proof (rw_cells_merge asegs m3 A [] [CB (Z.to_nat len) (firstn (Z.to_nat len) data); CB (length bs) bs] _ J1) as J2.
        cbn [app cells_size cells_bytes Cells.csize Cells.cbytes] in J2. rewrite app_nil_r, BS in J2.
        replace (Z.to_nat len + (length bs + 0))%nat with (Z.to_nat (len + n)) in J2 by lia.
        replace (Z.to_nat (cap - (len + n))) with (Z.to_nat (cap - len - n)) by lia. exact J2. }
      (* [comment removed for export] *)
      assert (RSC3 : exists stj', rw_cells asegs m3 ARS [CB RSN stj']).
      { assert (J1 : rw_cells asegs m3 ARS ([CB (length bs) bs] ++ ([CB (Z.to_nat want - length bs) (skipn (length bs) (firstn (Z.to_nat want) stj))] ++ [CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))]))).
        { apply (proj2 (rw_cells_app _ _ _ _)). split; [exact RSC2a3|]. cbn [cells_size Cells.csize Nat.add].
          replace (ARS + Z.of_nat (length bs + 0)) with (ARS + n) by lia.
          apply (proj2 (rw_cells_app _ _ _ _)). split; [exact RSC2b3|].
          cbn [cells_size Cells.csize Nat.add]. replace (ARS + n + Z.of_nat (Z.to_nat want - length bs + 0)) with (ARS + want) by lia. exact RSCb3. }
        cbn [app] in J1.
        pose proof (rw_cells_merge asegs m3 ARS [] [_; _; _] [] J1) as J2. cbn [app cells_size cells_bytes Cells.csize Cells.cbytes] in J2. rewrite ?app_nil_r in J2.
        eexists. replace RSN with (length bs + (Z.to_nat want - length bs + (Z.to_nat (65536 - want) + 0)))%nat by (pose proof RSN_Z; lia). exact J2. }
      assert (IV3 : INV (len + n) cap A TRS B np (firstn (Z.to_nat (cap - len - n)) (skipn (Z.to_nat n) junk)) m3 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo) g).
      { split; [exact ST3|]. split; [exact MI3|]. split; [exact FR3|]. split; [exact DS3|]. split; [exact DIC3|]. split; [exists e; exact ER3|]. split; [exact IFL3|].
        split; [exact SOF3|]. split; [exact SEF3|]. split; [exact SIF3|]. split; [exact SSZ3|]. split; [exact BY3|]. split; [exact HART3|]. split; [exact HT|].
        split; [exact NP|]. split; [exact HB|].
        split; [exact DM2|]. split; [exact FL|]. split; [exact BLK3|]. split; [exact SOK3|]. split; [exact RSC3|].
        split; [exists k; split; [exact CAP| exact HDRV3]|]. unfold zlength in *. lia. }
      clear FR3 DS3 DIC3 IFL3 SOF3 SEF3 SIF3 SSZ3 BY3 BLK3 RSC3.
      (* [comment removed for export] *)
      unfold wz.
      do 3 step. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        apply evt_done. assert (E : len + n = cap) by (rewrite ?unsigned_lit in K by lia; lia).
        rewrite E in IV3 |- *. replace (n + len) with cap by lia.
        eapply (loop_grow cap A TRS B np _ m3 _ g (zlength data - len) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IV3 IH); unfold zlength in *; lia.
      + (* [comment removed for export] *)
        do 2 step. apply evt_done.
        eapply (IH (len + n) cap A TRS B np _ m3 _ g _ IV3); [rewrite ?unsigned_lit in K by lia; lia| | lia].
        unfold loop_regs. unfold wz. nexists 17%nat. replace (n + len) with (len + n) by lia. reflexivity.
    - (* [comment removed for export] *)
      apply evt_done.
      assert (EOFL : len = zlength data) by (rewrite ?unsigned_lit in K by lia; unfold zlength in *; lia).
      assert (N0 : n = 0) by (rewrite ?unsigned_lit in K by lia; lia).
      assert (RSC3 : exists stj', rw_cells asegs m2 ARS [CB RSN stj']).
      { assert (BS0 : length bs = 0%nat) by (clear - N0; subst n; lia).
        apply length_zero_iff_nil in BS0. rewrite BS0 in RSC2.
        cbn [length cells_size] in RSC2.
        assert (J1 : rw_cells asegs m2 ARS ([CB (Z.to_nat want - 0) (skipn 0 (firstn (Z.to_nat want) stj))] ++ [CB (Z.to_nat (65536 - want)) (firstn (Z.to_nat (65536 - want)) (skipn (Z.to_nat want) stj))])).
        { apply (proj2 (rw_cells_app _ _ _ _)). split.
          - pose proof (proj2 (proj1 (rw_cells_app m2 ARS [CB 0 []] _) RSC2)) as R. cbn [cells_size Cells.csize Nat.add] in R. rewrite Z.add_0_r in R. exact R.
          - cbn [cells_size Cells.csize Nat.add]. replace (ARS + Z.of_nat (Z.to_nat want - 0 + 0)) with (ARS + want) by lia. exact RSCb2. }
        pose proof (rw_cells_merge asegs m2 ARS [] [_; _] [] J1) as J2. cbn [app cells_size cells_bytes Cells.csize Cells.cbytes] in J2. rewrite ?app_nil_r in J2.
        eexists. replace RSN with (Z.to_nat want - 0 + (Z.to_nat (65536 - want) + 0))%nat by (pose proof RSN_Z; lia). exact J2. }
      assert (IV2 : INV len cap A TRS B np junk m2 (with_fds (FDS3 (FdFile path (Z_to_bv 64 (len + n)))) mo) g).
      { split; [exact ST2|]. split; [exact MI2|]. split; [exact FR2|]. split; [exact DS2|]. split; [exact DIC2|]. split; [exists e; exact ER2|]. split; [exact IFL2|].
        split; [exact SOF2|]. split; [exact SEF2|]. split; [exact SIF2|]. split; [exact SSZ2|]. split; [exact BY2|].
        split; [rewrite N0, Z.add_0_r in HART2; rewrite N0, Z.add_0_r; exact HART2|]. split; [exact HT|]. split; [exact NP|]. split; [exact HB|].
        split; [rewrite N0, Z.add_0_r in DM2 |- *; exact DM2|]. split; [exact FL|].
        split; [exact BLK2|]. split; [exact SOK2|]. split; [exact RSC3|].
        split; [exists k; split; [exact CAP| rewrite N0, Z.add_0_r in HDRV2; rewrite N0, Z.add_0_r; exact HDRV2]|]. unfold zlength in *. lia. }
      rewrite N0, Z.add_0_r in IV2 |- *. subst len.
      unfold Kloop.
      rewrite ?unsigned_lit by lia.
      eapply POST; [exact IV2| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma loop_want : forall (len cap A : Z) TRS B np junk m mo g (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      INV len cap A TRS B np junk m mo g -> HEAD_OK (zlength data - len) -> len < cap ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) (wz A) a0 a1 a2 a3 a4 a5 a6 a7 (wz P1) (wz len) (wz 3) (wz cap) (wz ARS) s7 q8 q9 q10 q11 t3 t4 t5 t6)
                    F (wz 0x81f84) fc None m (seg_rom asegs)) mo g
          (Kloop data fs cap).
  Proof.
    intros until t6. intros IV IH LT.
    pose proof IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (k & CAP & _) & LEN1 & LEN2 & CAP2).
    unfold wz.
    apply lrz_step_evt.
    step. rewrite ?(unsigned_lit len), ?(unsigned_lit cap) by lia. do 2 step. if_cases K; zify_cond K.
    - apply evt_done. apply (loop_read len cap A TRS B np junk m mo g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cap - len) IV IH LT); lia.
    - step. apply evt_done. apply (loop_read len cap A TRS B np junk m mo g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 65536 IV IH LT); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma head_ok : forall n : nat, HEAD_OK (Z.of_nat n).
  Proof.
    induction n as [|n IHn]; intros len cap A TRS B np junk m mo g ms IV LT RG LT'.
    - exfalso. destruct IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEN1 & LEN2 & _). unfold zlength in *. lia. (* [comment removed for export] *)
    - pose proof (head_ok_mono _ (zlength data - len) IHn ltac:(lia)) as IH. (* [comment removed for export] *)
      (nelim RG 18%nat; intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 ->).
      apply (loop_want len cap A TRS B np junk m mo g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IV IH LT).
  Qed.

  Theorem loop_ok : loop_stmt AI DI TI sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
  Proof.
    intros len cap A TRS B np junk m mo g ms IV LT RG.
    pose proof IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEN1 & LEN2 & _). (* [comment removed for export] *)
    apply (head_ok (S (Z.to_nat (zlength data))) len cap A TRS B np junk m mo g ms IV LT RG). unfold zlength in *. lia.
  Qed.
End S.

(* [comment removed for export] *)
Theorem loop_proof : forall (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface),
  drv_traces_ok TI -> so_exit_stmt -> so_diag_refused_stmt -> so_diag_read_error_stmt ->
  forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (fs : Fs) (lo SPB P1 : Z) (tid ra0 : word)
         (path slack data : list byte) (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 : word),
    loop_side sp tp fc lo SPB P1 tid path slack ->
    post_stmt AI DI TI sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11 ->
    loop_stmt AI DI TI sp gp tp F fc fs lo SPB P1 tid ra0 path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.
Proof.
  intros AI DI TI TROK SE SR SRD. intros until q11. intros (TP & LO & GT & SPH & SPBE & TID & FRM & NONUL & SLK & LEN & PUS & PHI & SPAL & WIN & BOT) POST.
  eapply loop_ok; eassumption.
Qed.

End CeilWrap.
End Drv_loop.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
Module Drv_open.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Namei.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.LRzAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_syscalls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art Drv_exit Drv_die OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_read OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_xport OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_hooks.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface).
  Let ART := CJ_iface.ART AI.
  Let ADRV := Drv_iface2.ADRV AI DI.
  Hypothesis TROK : drv_traces_ok TI.
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_OOM : so_diag_oom_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.
  Hypothesis SO_CANTOPEN : so_diag_cannot_open_stmt.
  (* [comment removed for export] *)
  Hypothesis ARGV_OK : forall sp0 LB LF SP a, SP <= a < 2^47 -> cj_client_addr sp0 LB LF SP a.

  Lemma cj_pres_bytes_at_hi : forall sp0 LB LF SP m m' A bs,
    cj_pres sp0 LB LF SP m m' -> bytes_at asegs m A bs -> SP <= A -> A + Z.of_nat (length bs) <= 2^47 -> bytes_at asegs m' A bs.
  Proof.
    intros sp0 LB LF SP m m' A bs HP (H0 & H1 & HB) HS HH. split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite <- (HB i Hi). unfold mrd.
    destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply ARGV_OK; lia)) as [E _]. rewrite E. reflexivity.
  Qed.

  Local Ltac ivs := unfold adstat_easy, AIMG_HI, AERRNO, AINITFLAG, ATP; exit_lits; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

  (* [comment removed for export] *)
  Lemma after_open_ok :
    forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (fs : Fs) (e3 : FdEntry) (lo P1 : Z) (tid : word) (path slack fj : list byte) (errv v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word)
           (TRS : list (list Z)) (B np : Z) (KH : TSet),
      DMOD fs (FDS3 e3) mo -> ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [] [] TRS B m mo g -> TINV TI np TRS ->
      ADRV (S (loop_tokens 0)) m mo g -> cost_malloc 65536 + loop_budget 65536 <= B -> tp = wz ATP ->
      stk asegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp + 80 -> alloc_ceiling <= lo -> bv_unsigned sp + 128 <= 2^47 ->
      mem_inv asegs m -> frm0 fc -> ADSTAT tid m -> 0 < bv_unsigned tid < 2^22 -> DICPT m ->
      rw_cells asegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
      rw_cells asegs m AERRNO [C4 errv] -> rw_cells asegs m AINITFLAG [C1 (Z_to_bv 8 0)] ->
      stdout_file m stdout_init -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
      (exists stj, rw_cells asegs m ARS [CB RSN stj]) ->
      bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
      (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 128 <= P1 ->
      P1 + zlength path + 1 + zlength slack + 16 <= 2^47 ->
      KH [] ->
      (forall (m' : word -> option byte) (mo' : Model) (g' : lghost) (A : Z) (junk : list byte) (e' : word) (TRS' : list (list Z)) ms',
          stk asegs m' lo (bv_unsigned sp) -> mem_inv asegs m' -> ADSTAT tid m' -> DICPT m' ->
          rw_cells asegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0) ->
          rw_cells asegs m' AERRNO [C4 e'] -> rw_cells asegs m' AINITFLAG [C1 (Z_to_bv 8 0)] ->
          stdout_file m' stdout_init -> stderr_wfile0 m' -> stdin_file m' -> stack_shadow_zero m' ->
          (exists stj, rw_cells asegs m' ARS [CB RSN stj]) ->
          bytes_at asegs m' P1 (path ++ Z_to_bv 8 0 :: slack) ->
          ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [(A, 65536)] [] TRS' (B - cost_malloc 65536) m' mo' g' -> TINV TI np TRS' ->
          ADRV (loop_tokens 0) m' mo' g' ->
          DMOD fs (FDS3 e3) mo' -> ablock_range A 65536 -> rw_cells asegs m' A [CB (Z.to_nat 65536) junk] ->
          loop_regs sp gp tp F fc P1 s8 s9 s10 s11 0 65536 A m' 0x81f84 ms' ->
          LRZ asegs ms' mo' g' KH) ->
      LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 (wz 2) s1 (wz 3) a1 a2 a3 a4 a5 a6 a7 (wz P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x81ef8) fc None m (seg_rom asegs)) mo g
          KH.
  Proof.
    intros until KH. intros DM HART HT HDRV HB TP ST LO GT SPH MI FRM DS TID DIC FR ER IFL SOF SEF SIF SSZ [stj RSC] BY NONUL SLK LEN PUS PHI KH0 HK.
    pose proof RSN_Z as HRSN. pose proof ARS_eq as HARS.
    pose proof DM as [HH MFDS HFS].
    (* [comment removed for export] *)
    assert (Ecm : cost_malloc 65536 = ltac:(let v := eval vm_compute in (cost_malloc 65536) in exact v)) by (vm_compute; reflexivity).
    assert (Elb : loop_budget 65536 = ltac:(let v := eval vm_compute in (loop_budget 65536) in exact v)) by (vm_compute; reflexivity). rewrite Ecm, Elb in HB.
    unfold wz in *. unfold AERRNO, ATP in ER. unfold AINITFLAG in IFL.
    apply lrz_step_evt.
    step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    do 4 step. apply evt_done.
    eapply (drv_malloc_nn AI TI TROK DI (loop_tokens 0)) with (lo := lo) (np := np) (n := 65536);
      first [ exact HART | exact HDRV | exact HT | exact ST | exact MI | exact TP | reflexivity
            | unfold AERRNO, ATP; exact ER
            | unfold S_DRIVER; rewrite unsigned_lit by lia; cbn; tauto
            | rewrite Ecm; lia
            | unfold DRV_BFLOOR; lia
            | intros EP; exfalso; pose proof (is_primary_bound 65536 ltac:(lia) EP); lia
            | unfold DRV_REQ_MAX; lia
            | rewrite ?unsigned_lit by lia; unfold AMALLOC_STACK; lia
            | idtac ].
    (* [comment removed for export] *)
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 g2 errv2 TRS2 A junk MI2 ST2 ER2 PR GM HT2 HV NZ BR NI HA2 HD2 BLK.
    pose proof (DMOD_vm_only _ _ _ _ DM HV) as DM2.
    replace (ret_pc (Z_to_bv 64 0x81f0c)) with (Z_to_bv 64 0x81f0c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (DS2 : ADSTAT tid m2) by (eapply ADSTAT_cj_pres; [exact DS| exact PR]).
    assert (DI2 : DICPT m2) by (eapply DICPT_cj_pres; [exact DIC| exact PR]).
    assert (SOF2 : stdout_file m2 stdout_init) by (eapply stdout_file_cj_pres; [exact SOF| exact PR]).
    assert (SEF2 : stderr_wfile0 m2) by (eapply stderr_wfile0_cj_pres; [exact SEF| exact PR]).
    assert (SIF2 : stdin_file m2) by (eapply stdin_file_cj_pres; [exact SIF| exact PR]).
    assert (SSZ2 : stack_shadow_zero m2) by (eapply stack_shadow_zero_cj_pres; [exact SSZ| exact PR| exact (art_lowshadow AI _ _ _ _ _ _ _ _ _ HA2)]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0))
      by (eapply cj_pres_rw_cells; [exact PR| exact FR| left; unfold mframe; cbn; lia]).
    assert (IFL2 : rw_cells asegs m2 AINITFLAG [C1 (Z_to_bv 8 0)])
      by (eapply cj_pres_rw_cells; [exact PR| exact IFL| apply cj_client_range_img; unfold AINITFLAG, ADATA_LO, AIMG_HI, AERRNO, ATP; cbn; lia]).
    assert (RSC2 : rw_cells asegs m2 ARS [CB RSN stj])
      by (eapply cj_pres_rw_cells; [exact PR| exact RSC| apply cj_client_range_img; unfold ARS, ADATA_LO, AIMG_HI, AERRNO, ATP; cbn; lia]).
    assert (BY2 : bytes_at asegs m2 P1 (path ++ Z_to_bv 8 0 :: slack)).
    { pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
      eapply cj_pres_bytes_at_hi; [exact PR| exact BY| lia| rewrite length_app; cbn [length]; unfold zlength in *; lia]. }
    (nelimp BR 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    apply lrz_step_evt. unfold wz. step. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    do 4 step. step. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
    do 2 step. apply evt_done.
    eapply (HK m2 mo2 g2 A junk errv2 TRS2);
      [ exact ST2 | exact MI2 | exact DS2 | exact DI2 | exact FR2 | unfold AERRNO, ATP; exact ER2 | exact IFL2
      | exact SOF2 | exact SEF2 | exact SIF2 | exact SSZ2 | exists stj; exact RSC2 | exact BY2 | exact HA2 | exact HT2 | exact HD2
      | exact DM2 | exact BR | exact BLK | ].
    unfold loop_regs, ARS. repeat eexists.
  Qed.

  (* [comment removed for export] *)
  Lemma dir_read :
    forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (fs : Fs) (lo P1 A : Z) (tid : word) (path slack : list byte) (errv q8 q9 q10 q11 : word)
           (TRS : list (list Z)) (B : Z) (stj : list byte) ms,
      DMOD fs (FDS3 FdDir) mo -> ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [(A, 65536)] [] TRS B m mo g -> tp = wz ATP ->
      stk asegs m lo (bv_unsigned sp) -> lo + 2^22 <= bv_unsigned sp + 80 -> alloc_ceiling <= lo -> bv_unsigned sp + 128 <= 2^47 ->
      mem_inv asegs m -> frm0 fc -> ADSTAT tid m -> 0 < bv_unsigned tid < 2^22 -> DICPT m ->
      rw_cells asegs m AERRNO [C4 errv] ->
      stdout_file m stdout_init -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m ->
      bytes_at asegs m P1 (path ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) path ->
      (- (P1 + zlength path + 1)) mod 8 <= zlength slack -> zlength path <= 131071 -> bv_unsigned sp + 128 <= P1 ->
      P1 + zlength path + 1 + zlength slack + 16 <= 2^47 ->
      rw_cells asegs m ARS [CB RSN stj] ->
      loop_regs sp gp tp F fc P1 q8 q9 q10 q11 0 65536 A m 0x81f84 ms ->
      LRZ asegs ms mo g (t_die (msg_read_error path) fs).
  Proof.
    intros until ms. intros DM HART TP ST LO GT SPH MI FRM DS TID DIC ER SOF SEF SIF SSZ BY NONUL SLK LEN PUS PHI RSC nelH_; (nelim nelH_ 18%nat; intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 ->)
.
    pose proof RSN_Z as HRSN. pose proof ARS_eq as HARS.
    pose proof DM as [MFDS HFS HH].
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ A 65536 HART ltac:(left; reflexivity)) as BR.
    (nelimp BR 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    pose proof (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) as (IC & _).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART) as LOW.
    unfold wz in *. unfold AERRNO, ATP in ER.
    apply lrz_step_evt.
    do 3 step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 3 step.
    step.                                   (* [comment removed for export] *)
    apply evt_done.
    eapply (lrz_impl_read_dir asegs _ _ mo g 3 (bv_unsigned (Z_to_bv 64 ARS)) 65536);
      [| rewrite MFDS; reflexivity| rewrite rw_bytes_max_val; lia| rewrite unsigned_lit by (unfold ARS; lia); rewrite TASK_SIZE_val; unfold ARS; lia|].
    { eapply read_icpt_ok with (lo := lo) (junk := stj) (errv := errv);
        [ exact IC | exact (proj1 DIC) | exact MI | exact ST | exact GT | unfold AREAD_STACK; lia
        | rewrite unsigned_lit by (unfold ARS; lia); exact RSC
        | change (errno_addr tp) with (bv_unsigned tp + -164); rewrite (errno_addr_tp tp TP); unfold AERRNO, ATP; exact ER
        | reflexivity | reflexivity | exact TP | lia | lia
        | rewrite unsigned_lit by (unfold ARS; lia); unfold stage_range, RS_LO, RS_HI, ARS; lia
        | rewrite unsigned_lit by (unfold ARS; lia); apply (lowsh_rs_shadow_ok m ARS 65536 LOW); unfold ARS; lia
        | rewrite unsigned_lit by (unfold ARS; lia); unfold ARS; lia ]. }
    intros ms2 PO.
    (nelim PO 23%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 RSC2 ER2 He).
    cbn [read_ret] in *. change (errno_addr tp) with (bv_unsigned tp + -164) in MU2, ER2. rewrite (errno_addr_tp tp TP) in MU2, ER2.
    rewrite ?unsigned_lit in MU2 by (unfold ARS; lia).
    replace (ret_pc (Z_to_bv 64 0x81fa0)) with (Z_to_bv 64 0x81fa0 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply lrz_step_evt. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K. apply evt_done.
    axport DS MU2 WM2 DS2. axport DIC MU2 WM2 DIC2. axport SOF MU2 WM2 SOF2. axport SEF MU2 WM2 SEF2. axport SIF MU2 WM2 SIF2.
    axport SSZ MU2 WM2 SSZ2. axport BY MU2 WM2 BY2.
    assert (HART2 : ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [(A, 65536)] [] TRS B m2 mo g).
    { eapply (art_frame AI); [exact HART| exact MU2| exact WM2|].
      apply Forall_cons; [apply cj_write_ok_stack; [unfold AREAD_STACK|]; lia|].
      apply Forall_cons; [apply cj_write_ok_img; unfold ARS, ADATA_LO, AIMG_HI; cbn [fst snd]; lia|].
      apply Forall_cons; [apply cj_write_ok_errno| apply Forall_nil]. }
    eapply (die_readerr AI SO_EXIT SO_READERR) with (lo := lo) (tid := tid) (sp0 := bv_unsigned sp + 128) (SPB := bv_unsigned sp + 80)
                                                    (LB := [(A, 65536)]) (TRS := TRS) (B := B) (P1 := P1) (slack := slack);
      [ exact DM | right; eexists; reflexivity | exact TP | exact GT | lia | lia | lia | exact TID | exact FRM
      | | reflexivity | exact BY2 | exact NONUL | exact SLK | unfold zlength in *; lia | lia | exact PHI ].
    split; [exact ST2|]. split; [exact MI2|]. split; [exact DS2|]. split; [exact DIC2|]. split; [exact SOF2|]. split; [exact SEF2|].
    split; [exact SIF2|]. split; [exact SSZ2| exact HART2].
  Qed.

  Hypothesis LOOP : forall sp gp tp F fc fs lo SPB P1 tid path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11,
    loop_side sp tp fc lo SPB P1 tid path slack ->
    loop_stmt AI DI TI sp gp tp F fc fs lo SPB P1 tid (wz ASTAGE2_RET) path slack data fj v0 v1 v2 v3 v4 v5 v6 v7 q8 q9 q10 q11.

  Theorem main_two_proof : main_two_stmt AI DI TI.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo g fs lo P1 tid path slack errv B0.
    intros DM HART HB0 HDRV HT0 _ RA TP -> -> ST LO CEIL SPH WIN SPAL BOT MI FRM DS TID DIC ER IFL SOF SEF SIF SSZ [stj RSC] AV BY NONUL SLASH DOTDOT SLK LEN PUS PHI.
    pose proof RSN_Z as HRSN. pose proof ARS_eq as HARS.
    pose proof DM as [MFDS HFS HH].
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof CEIL as GT.
    assert (Elb : loop_budget 65536 = ltac:(let v := eval vm_compute in (loop_budget 65536) in exact v)) by (vm_compute; reflexivity).
    assert (Ecm : cost_malloc 65536 = ltac:(let v := eval vm_compute in (cost_malloc 65536) in exact v)) by (vm_compute; reflexivity).
    unfold wz, AMAIN in *. unfold AERRNO, ATP in ER. unfold AINITFLAG in IFL.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    apply lrz_step_evt.
    carve_frame 80%nat ST.
    do 12 step.
    if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    do 4 step.
    apply evt_done.
    name_sp sp (-80).
    rewrite <- Hsp in FR, ST. replace (bv_unsigned sp + 64) with (bv_unsigned sp0 + 144) in AV by lia.
    assert (LO' : lo + 2^22 <= bv_unsigned sp0 + 80) by lia. assert (PUS' : bv_unsigned sp0 + 128 <= P1) by lia.
    assert (SPH' : bv_unsigned sp0 + 128 <= 2^47) by lia.
    assert (SPAL' : bv_unsigned sp0 mod 16 = 0) by (rewrite Hsp, Z.add_mod, SPAL by lia; reflexivity).
    assert (WIN' : sp_window_lo <= bv_unsigned sp0 + 128) by lia.
    assert (BOT' : ASTACK_BOTTOM (bv_unsigned sp0 + 128) <= lo) by (replace (bv_unsigned sp0 + 128) with (bv_unsigned sp + 48) by lia; exact BOT).
    rewrite <- Hsp in MU. replace (bv_unsigned sp) with (bv_unsigned sp0 + 80) in MU by lia.
    replace (bv_unsigned sp + 48) with (bv_unsigned sp0 + 128) in HART by lia. replace (bv_unsigned sp) with (bv_unsigned sp0 + 80) in HART by lia.
    clear Hsp Esp LO PUS SPH SPAL WIN BOT. clear sp. rename sp0 into sp.
    (* [comment removed for export] *)
    lazymatch type of MU with munch _ _ ?mm => first [rename mm into m1 | idtac] end.   (* [comment removed for export] *)
    lazymatch goal with |- LRZ _ (MS _ _ _ _ _ ?m1 _) _ _ _ =>
      axport DS MU WM DS1; axport DIC MU WM DIC1; axport SOF MU WM SOF1; axport SEF MU WM SEF1; axport SIF MU WM SIF1; axport SSZ MU WM SSZ1;
      assert (HART1 : ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [] [] [] B0 m1 mo g)
        by (eapply (art_frame AI); [exact HART| exact MU| exact WM| apply Forall_cons; [apply cj_write_ok_stack; lia| apply Forall_nil]]);
      assert (HDRV1 : ADRV DRV_CALLS m1 mo g)
        by (eapply (adrv_frame AI DI); [exact HART| exact HDRV| exact MU| exact WM| apply Forall_cons; [apply cj_write_ok_stack; lia| apply Forall_nil]])
    end.
    clear DS DIC SOF SEF SIF SSZ HART HDRV MU WM.   (* [comment removed for export] *)
    (nelim (ADSTAT_ssp tid _ DS1) 3%nat; intros cn0 [SSP1 SSP2] _). unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (BYP : bytes_at asegs m1 P1 (path ++ [Z_to_bv 8 0])).
    { replace (path ++ Z_to_bv 8 0 :: slack) with ((path ++ [Z_to_bv 8 0]) ++ slack) in BY by (rewrite <- app_assoc; reflexivity).
      exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) BY)). }
    (* [comment removed for export] *)
    assert (KERR : forall (e : Z) ms2,
      open_post (Z_to_bv 64 0x81ef8) sp gp tp (Z_to_bv 64 2) s1 (Z_to_bv 64 P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned (Z_to_bv 64 P1)) path errv cn0 lo m1 (SErr e) ms2 ->
      LRZ asegs ms2 mo g (t_die (msg_cannot_open path) fs)).
    { intros e ms2 PO. rewrite (unsigned_lit P1) in PO by lia.
      (nelim PO 25%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2 BY2 G1 G2 He).
      cbn [open_ret open_errno] in *. change (errno_addr tp) with (bv_unsigned tp + -164) in MU2, ER2. rewrite (errno_addr_tp tp TP) in MU2, ER2.
      replace (ret_pc (Z_to_bv 64 0x81ef8)) with (Z_to_bv 64 0x81ef8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply lrz_step_evt. step. if_cases K; zify_cond K; [| exfalso; lia]. clear K. apply evt_done.
      axport DS1 MU2 WM2 DS2. axport DIC1 MU2 WM2 DIC2. axport SOF1 MU2 WM2 SOF2. axport SEF1 MU2 WM2 SEF2. axport SIF1 MU2 WM2 SIF2.
      axport SSZ1 MU2 WM2 SSZ2. axport BY MU2 WM2 BY3.
      assert (HART2 : ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [] [] [] B0 m2 mo g).
      { eapply (art_frame AI); [exact HART1| exact MU2| exact WM2|].
        apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit|]; lia|]. apply Forall_cons; [apply cj_write_ok_errno| apply Forall_nil]. }
      eapply (die_cantopen AI SO_EXIT SO_CANTOPEN) with (lo := lo) (tid := tid) (sp0 := bv_unsigned sp + 128) (SPB := bv_unsigned sp + 80)
                                                        (LB := []) (TRS := []) (B := B0) (P1 := P1) (slack := slack);
        [ exact DM | left; reflexivity | exact TP | exact CEIL | lia | lia | lia | exact TID | exact FRM
        | | reflexivity | exact BY3 | exact NONUL | exact SLK | unfold zlength in *; lia | lia | exact PHI ].
      split; [exact ST2|]. split; [exact MI2|]. split; [exact DS2|]. split; [exact DIC2|]. split; [exact SOF2|]. split; [exact SEF2|].
      split; [exact SIF2|]. split; [exact SSZ2| exact HART2]. }
    (* [comment removed for export] *)
    lazymatch goal with |- LRZ _ ?ms _ _ _ =>
      eassert (OPEN : impl asegs (at_node asegs) (enode (NOpen path) dec_open) _ ms) end.
    { eapply open_spec with (lo := lo) (errv := errv) (canary := cn0);
        [ exact ST | rewrite unsigned_lit by lia; exact BYP
        | change (errno_addr tp) with (bv_unsigned tp + -164); rewrite (errno_addr_tp tp TP); unfold AERRNO, ATP; exact ER
        | exact SSP1 | exact SSP2 | exact MI | reflexivity | exact NONUL | lia
        | try (change (errno_addr tp) with (bv_unsigned tp + -164); rewrite (errno_addr_tp tp TP)); rewrite ?TP; unfold AERRNO, ATP, F_syscalls.got_ssp, F_syscalls.ssp_guard;
          rewrite ?unsigned_lit by lia; lia .. ]. }
    (* [comment removed for export] *)
    unfold spec_path.
    destruct (Nat.leb_spec0 4096 (length path)) as [TL|NTL].
    { eapply (lrz_impl_openat_toolong asegs); [exact OPEN| exact TL| intros ms2 PO; exact (KERR _ _ PO)]. }
    destruct (list_byte_eqb path []) eqn:E0.
    { apply list_byte_eqb_eq in E0. subst path. eapply (lrz_impl_openat_empty asegs); [exact OPEN| intros ms2 PO; exact (KERR _ _ PO)]. }
    apply list_byte_eqb_neq in E0.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?fj :: _) => set (fj0 := fj) in FR end.
    assert (KOK : forall (e3 : FdEntry) (KH : TSet) ms2,
      open_post (Z_to_bv 64 0x81ef8) sp gp tp (Z_to_bv 64 2) s1 (Z_to_bv 64 P1) s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned (Z_to_bv 64 P1)) path errv cn0 lo m1
                (SVal (bv_unsigned (alloc_fd (m_fds mo)))) ms2 ->
      KH [] ->
      (forall (m' : word -> option byte) (mo' : Model) (g' : lghost) (A : Z) (junk : list byte) (e' : word) (TRS' : list (list Z)) ms',
          stk asegs m' lo (bv_unsigned sp) -> mem_inv asegs m' -> ADSTAT tid m' -> DICPT m' ->
          rw_cells asegs m' (bv_unsigned sp) (mframe fj0 s0 s1 s2 s3 s4 s5 s6 s7 (wz ASTAGE2_RET)) ->
          rw_cells asegs m' AERRNO [C4 e'] -> rw_cells asegs m' AINITFLAG [C1 (Z_to_bv 8 0)] ->
          stdout_file m' stdout_init -> stderr_wfile0 m' -> stdin_file m' -> stack_shadow_zero m' ->
          (exists stj', rw_cells asegs m' ARS [CB RSN stj']) ->
          bytes_at asegs m' P1 (path ++ Z_to_bv 8 0 :: slack) ->
          ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [(A, 65536)] [] TRS' (B0 - cost_malloc 65536) m' mo' g' -> TINV TI 0 TRS' ->
          ADRV (loop_tokens 0) m' mo' g' ->
          DMOD fs (FDS3 e3) mo' -> ablock_range A 65536 -> rw_cells asegs m' A [CB (Z.to_nat 65536) junk] ->
          loop_regs sp gp tp F fc P1 s8 s9 s10 s11 0 65536 A m' 0x81f84 ms' ->
          LRZ asegs ms' mo' g' KH) ->
      LRZ asegs ms2 (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) e3) mo) g KH).
    { intros e3 KH ms2 PO KH0 HK. rewrite MFDS, FDS0_insert. rewrite MFDS, FDS0_alloc in PO. unfold wz in PO. rewrite (unsigned_lit 3) in PO by lia. rewrite (unsigned_lit P1) in PO by lia.
      (nelim PO 25%nat; intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m2 -> MU2 WM2 MI2 ST2 ER2 BY2 G1 G2 Hfd).
      cbn [open_ret open_errno] in *. change (errno_addr tp) with (bv_unsigned tp + -164) in MU2, ER2. rewrite (errno_addr_tp tp TP) in MU2, ER2.
      replace (ret_pc (Z_to_bv 64 0x81ef8)) with (Z_to_bv 64 0x81ef8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      axport DS1 MU2 WM2 DS2. axport DIC1 MU2 WM2 DIC2. axport FR MU2 WM2 FR2. axport IFL MU2 WM2 IFL2. axport SOF1 MU2 WM2 SOF2.
      axport SEF1 MU2 WM2 SEF2. axport SIF1 MU2 WM2 SIF2. axport SSZ1 MU2 WM2 SSZ2. axport BY MU2 WM2 BY3. axport RSC MU2 WM2 RSC2.
      rewrite RA in FR2.
      assert (HART2 : ART (bv_unsigned sp + 128) (bv_unsigned sp + 80) [] [] [] B0 m2 (with_fds (FDS3 e3) mo) g).
      { apply (art_model_frame AI _ _ _ _ _ _ m2 mo (with_fds (FDS3 e3) mo) g); [| reflexivity| reflexivity| exact HH].
        eapply (art_frame AI); [exact HART1| exact MU2| exact WM2|].
        apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit|]; lia|]. apply Forall_cons; [apply cj_write_ok_errno| apply Forall_nil]. }
      assert (HDRV2 : ADRV (S (loop_tokens 0)) m2 (with_fds (FDS3 e3) mo) g).
      { apply (adrv_weaken AI DI DRV_CALLS); [| unfold DRV_CALLS, loop_tokens; lia].
        apply (adrv_model AI DI DRV_CALLS m2 mo (with_fds (FDS3 e3) mo) g); [| reflexivity| reflexivity| exact HH].
        eapply (adrv_frame AI DI); [exact HART1| exact HDRV1| exact MU2| exact WM2|].
        apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit|]; lia|]. apply Forall_cons; [apply cj_write_ok_errno| apply Forall_nil]. }
      eapply (after_open_ok _ sp gp tp _ _ _ s1 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 _ g fs e3 lo P1 tid path slack fj0 _ s0 s1 s2 s3 s4 s5 s6 s7 _ _ B0 0 KH);
        [ eapply DMOD_with_fds; exact DM | exact HART2 | exact HT0 | exact HDRV2 | unfold DRV_B_MAIN in HB0; lia | exact TP
        | exact ST2 | exact LO' | exact GT | exact SPH' | exact MI2 | exact FRM | exact DS2 | exact TID | exact DIC2 | exact FR2
        | unfold AERRNO, ATP; exact ER2 | unfold AINITFLAG; exact IFL2 | exact SOF2 | exact SEF2 | exact SIF2 | exact SSZ2 | exists stj; exact RSC2 | exact BY3
        | exact NONUL | exact SLK | exact LEN | exact PUS' | exact PHI | exact KH0 | exact HK ]. }
    destruct (list_byte_eqb path dot_path) eqn:E1.
    { (* [comment removed for export] *)
      apply list_byte_eqb_eq in E1. subst path. unfold t_opened_dir.
      eapply (lrz_impl_openat_dot asegs); [exact OPEN| rewrite MFDS; reflexivity| rewrite MFDS, FDS0_alloc; unfold wz; rewrite unsigned_lit by lia; lia
        | intros e ms2 He PO; exact (KERR _ _ PO) |].
      intros ms2 PO. apply (KOK FdDir _ ms2 PO); [apply t_emit_has_nil'|].
      intros m' mo' g' A junk' e' TRS' ms' ST' MI' DS' DIC' FR' ER' IFL' SOF' SEF' SIF' SSZ' [stj' RSC'] BY' HART' HT' HDRV' DM' BR BLK LR.
      eapply dir_read; [exact DM'| exact HART'| exact TP| exact ST'| exact LO'| exact GT| exact SPH'| exact MI'| exact FRM| exact DS'| exact TID| exact DIC'
                      | exact ER'| exact SOF'| exact SEF'| exact SIF'| exact SSZ'| exact BY'| exact NONUL| exact SLK| exact LEN| exact PUS'| exact PHI| exact RSC'| exact LR]. }
    apply list_byte_eqb_neq in E1.
    rewrite <- HFS in KERR, KOK |- *. destruct (fs_lookup (m_fs mo) path) as [data|] eqn:FL.
    - (* [comment removed for export] *)
      unfold t_opened.
      eapply (lrz_impl_openat_file asegs); [exact OPEN| lia| exact E0| exact E1| exact DOTDOT| exact SLASH| exact FL| rewrite MFDS; reflexivity| rewrite MFDS, FDS0_alloc; unfold wz; rewrite unsigned_lit by lia; lia
        | intros e ms2 He PO; exact (KERR _ _ PO) |].
      intros ms2 PO. apply (KOK (FdFile path (Z_to_bv 64 0)) (Kloop data (m_fs mo) 65536) ms2 PO).
      + apply Kloop_nil.
      + intros m' mo' g' A junk' e' TRS' ms' ST' MI' DS' DIC' FR' ER' IFL' SOF' SEF' SIF' SSZ' RSC' BY' HART' HT' HDRV' DM' BR BLK LR.
        assert (SIDE : loop_side sp tp fc lo (bv_unsigned sp + 80) P1 tid path slack).
        { split; [exact TP|]. split; [exact LO'|]. split; [exact GT|]. split; [exact SPH'|]. split; [reflexivity|]. split; [exact TID|].
          split; [exact FRM|]. split; [exact NONUL|]. split; [exact SLK|]. split; [exact LEN|]. split; [exact PUS'|]. split; [exact PHI|]. split; [exact SPAL'|]. split; [exact WIN'| exact BOT']. }
        destruct (art_shadow AI _ _ _ _ _ _ _ _ _ A 65536 HART' ltac:(left; reflexivity)) as [_ SOK'].
        eapply (LOOP sp gp tp F fc (m_fs mo) lo (bv_unsigned sp + 80) P1 tid path slack data fj0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SIDE
                  0 65536 A TRS' (B0 - cost_malloc 65536) 0 (firstn (Z.to_nat 65536) (skipn 0 junk')) m' mo' g' ms'); [| lia| exact LR].
        split; [exact ST'|]. split; [exact MI'|]. split; [exact FR'|]. split; [exact DS'|]. split; [exact DIC'|]. split; [exists e'; exact ER'|]. split; [exact IFL'|].
        split; [exact SOF'|]. split; [exact SEF'|]. split; [exact SIF'|]. split; [exact SSZ'|]. split; [exact BY'|]. split; [exact HART'|]. split; [exact HT'|].
        split; [reflexivity|]. split; [unfold DRV_B_MAIN in HB0; lia|].
        split; [exact DM'|]. split; [exact FL|]. split.
        { cbn [Z.to_nat firstn Z.sub]. replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity.
          eapply (rw_cells_split_CB asegs m' A [] (Z.to_nat 65536) junk' [] [0%nat; Z.to_nat 65536]) in BLK; [| reflexivity].
          cbn [mk_CB_cells firstn skipn app] in BLK. exact BLK. }
        split; [exact SOK'|]. split; [exact RSC'|].
        pose proof (bytes_at_bound _ _ _ _ BY) as BBd.
        split; [exists 0%nat; split; [reflexivity| exact HDRV']|]. unfold zlength. lia.
    - (* [comment removed for export] *)
      eapply (lrz_impl_openat_absent asegs); [exact OPEN| lia| exact E0| exact E1| exact DOTDOT| exact SLASH| exact FL| intros ms2 PO; exact (KERR _ _ PO)].
  Qed.
End S.


End CeilWrap.
End Drv_open.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_atexit.
Module Drv_trun.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_mem4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_xport OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_hooks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_atexit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cost_malloc_trun : forall n, 0 <= n <= 2^26 -> cost_malloc n <= cost_malloc (2^26).
Proof.
  intros n Hn. replace (cost_malloc (2^26)) with 268992576 by (vm_compute; reflexivity).
  unfold cost_malloc, asz, SEC_SLOT_TAX, CL24_TAX. destruct (is_primary n) eqn:E.
  - pose proof (is_primary_bound n ltac:(lia) E) as B. (nelimp (pslot_ok n ltac:(lia)) 3%nat; intros _ P _). destruct (is_cl24 n); lia.
  - unfold is_cl24. rewrite E. cbn [andb]. unfold smapsize, needed. rewrite E. unfold needed0. pose proof (rz_size_le n ltac:(lia)) as [_ R].
    pose proof (rounded8_le n ltac:(lia)) as R8.
    remember (rounded8 n) as r8. remember (rz_size n) as rz. unfold rounded8, roundup in *.
    Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma tcalls_pos : forall cl data b, 0 < cl -> nth_error data 2 = Some b ->
  Z.land (bv_unsigned b) 3 + 1 = Z.of_nat (tcalls cl data) /\ (1 <= tcalls cl data <= 4)%nat.
Proof.
  intros cl data b Hcl Hb. unfold tcalls. destruct (Z.to_nat cl) eqn:E; [lia|].
  rewrite (nth_error_nth _ _ _ Hb). change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  pose proof (Z.mod_pos_bound (bv_unsigned b) 4 ltac:(lia)). split; lia.
Qed.

Lemma tcalls_zero : forall data, tcalls 0 data = 1%nat.
Proof. intros data. reflexivity. Qed.

Section S.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface) (S_LIB : list (list Z)).
  Let ART := CJ_iface.ART AI.
  Let ADRV := Drv_iface2.ADRV AI DI.
  Hypothesis TROK : drv_traces_ok TI.
  Hypothesis LIBOK : forall tr, In tr S_LIB -> STAT TI tr.
  Hypothesis FUZZ : llvmfuzz_stmt AI TI S_LIB.
  Hypothesis SO_EMIT1 : so_emit_first_stmt.
  Hypothesis SO_EMIT2 : so_emit_again_stmt.
  Variables (sp gp tp : word) (fs : Fs) (lo SPB : Z) (tid : word)
            (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word) (ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 : word)
            (A cap : Z).
  Hypothesis TP : tp = wz ATP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 2^47.
  Hypothesis SPBE : SPB = bv_unsigned sp + 80.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis WIN : sp_window_lo <= bv_unsigned sp + 128.
  Hypothesis BOT : ASTACK_BOTTOM (bv_unsigned sp + 128) <= lo.
  Notation sp0 := (bv_unsigned sp + 128) (only parsing).

  Notation TRET := (trun_ret AI TI sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap).
  Notation MFRAME m := (rw_cells asegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)).
  Notation TFRAME m uj := (rw_cells asegs m (bv_unsigned sp - 80) [CB 8 uj; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (Z_to_bv 64 0x8202c)]).
  (* [comment removed for export] *)
  Notation EST pc Fv fcv mm rav x5 x6 x7 plen x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 cnt x28 x29 x30 x31 :=
    (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 plen) x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 AINITFLAG) (Z_to_bv 64 cnt) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fv (Z_to_bv 64 pc) fcv None mm (seg_rom asegs)) (only parsing).

  Lemma CEIL' : alloc_ceiling <= lo. Proof. try rewrite alloc_ceiling_lit. exact GT. Qed.

  (* [comment removed for export] *)
  Definition tpre (LB : list cblock) (TRS : list (list Z)) (B : Z) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
    ART sp0 SPB LB [] TRS B m mo g /\ In (A, cap) LB /\ TINV TI 0 TRS /\ 4 * FUZZ_NP (2^26) <= NPMAX TI
    /\ (exists e, rw_cells asegs m AERRNO [C4 e]) /\ mem_inv asegs m /\ stk asegs m lo (bv_unsigned sp - 80)
    /\ (exists uj, TFRAME m uj) /\ MFRAME m
    /\ ADSTAT tid m /\ DICPT m /\ stderr_wfile0 m /\ stdin_file m /\ stack_shadow_zero m /\ stdout_file m stdout_init
    /\ DMOD fs FDS0 mo /\ frm0 fc.

  (* [comment removed for export] *)
  Lemma trun_empty : forall (c : nat) LB TRS B (F : bvmap 5 word) fc m mo g (KT : TSet)
      rav x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    tpre LB TRS B fc m mo g -> 4 * FUZZ_COST (2^26) + 2 * cost_free <= B ->
    (1 <= c <= 4)%nat -> KT [] ->
    (forall ms' mo' g', TRET 0 (so_after (c - 1)) ms' mo' g' -> LRZ asegs ms' mo' g' KT) ->
    LRZ asegs (EST 0x82230 F fc m rav x5 x6 x7 0 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z.of_nat c) x28 x29 x30 x31) mo g
        (t_emit (W 1 emit_line) KT).
  Proof.
    intros until x31. intros PRE HB Hc HK KB.
    (nelim PRE 17%nat; intros HART INA HT NPOK ER MI ST TFR MFR DS DIC SEF SIF SSZ SOF DM FRM).
    pose proof (Z.mul_nonneg_nonneg (4 - Z.of_nat c) (FUZZ_NP (2^26)) ltac:(lia) (FUZZ_NP_pos _)) as NPK.
    pose proof (Z.mul_nonneg_nonneg (4 - Z.of_nat c) (FUZZ_COST (2^26)) ltac:(lia) (FUZZ_COST_pos (2^26) ltac:(lia))) as FCK.
    apply lrz_step_evt. unfold AINITFLAG. do 2 step. apply evt_done.
    change (Z_to_bv 64 6146256) with (Z_to_bv 64 AINITFLAG : word).
    eapply (trun_rounds AI TI S_LIB TROK LIBOK FUZZ SO_EMIT1 SO_EMIT2 sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11
              A cap (6146256 + 16) 0 0 [] TP LO GT SPH SPBE SPAL ltac:(lia) BOT ltac:(left; reflexivity) c LB TRS B 0 fc m mo g F KT);
      [| exact Hc| exact HK| exact KB].
    split; [exact HART|]. split; [exact INA|]. split; [left; reflexivity|]. split; [left; lia|].
    split; [exact HT|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact ER|]. split; [exact MI|]. split; [exact ST|]. split; [exact TFR|]. split; [exact MFR|].
    split; [exact DS|]. split; [exact DIC|]. split; [exact SEF|]. split; [exact SIF|]. split; [exact SSZ|]. split; [exact SOF|]. split; [exact DM| exact FRM].
  Qed.
  (* [comment removed for export] *)
  Lemma trun_copy : forall (c : nat) LB TRS B (F : bvmap 5 word) fc m mo g (KT : TSet) (D plen S : Z) (src junk' u : list byte) (e : word)
      x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    ART sp0 SPB ((D, plen) :: LB) [] TRS B m mo g -> In (A, cap) LB -> ~ In D (map fst LB) -> TINV TI 0 TRS -> 4 * FUZZ_NP (2^26) <= NPMAX TI ->
    4 * FUZZ_COST (2^26) + 2 * cost_free <= B ->
    rw_cells asegs m D [CB (Z.to_nat plen) junk'] -> bytes_at asegs m S src -> Z.of_nat (length src) = plen ->
    A <= S -> S + plen <= A + cap -> 0 < plen < 2^26 ->
    rw_cells asegs m AERRNO [C4 e] -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp - 80) -> TFRAME m u -> MFRAME m ->
    ADSTAT tid m -> DICPT m -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m -> stdout_file m stdout_init ->
    DMOD fs FDS0 mo -> frm0 fc ->
    (1 <= c <= 4)%nat -> KT [] ->
    (forall ms' mo' g', TRET 0 (so_after (c - 1)) ms' mo' g' -> LRZ asegs ms' mo' g' KT) ->
    LRZ asegs (EST 0x821ec F fc m (Z_to_bv 64 0x821ec) x5 x6 x7 plen (Z_to_bv 64 S) (Z_to_bv 64 D) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z.of_nat c) x28 x29 x30 x31) mo g
        (t_emit (W 1 emit_line) KT).
  Proof.
    intros until x31. intros HART INA NIN HT NPOK HB BLK SRC LSRC SA SB PL ER MI ST TFR MFR DS DIC SEF SIF SSZ SOF DM FRM Hc HK KB.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(right; exact INA)) 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ D plen HART ltac:(left; reflexivity)) 4%nat; intros BQ1 BQ2 BQ3 BQ4). unfold AIMG_HI in BQ1.
    pose proof (ablk_disj_band _ _ (art_block_band AI _ _ _ _ _ _ _ _ _ D plen HART ltac:(left; reflexivity))) as BDJ. unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in BDJ.
    assert (NE : D <> A) by (intros E; apply NIN; rewrite E; apply (in_map_fst_pair A cap); exact INA).
    pose proof (art_blocks_disjoint AI _ _ _ _ _ _ _ _ _ D plen A cap HART ltac:(left; reflexivity) ltac:(right; exact INA) NE) as DISJ.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ D plen HART ltac:(left; reflexivity)) as [_ SOKn].
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(right; exact INA)) as [_ SOKo].
    pose proof (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) as (IC & _).
    pose proof (Z.mul_nonneg_nonneg (4 - Z.of_nat c) (FUZZ_NP (2^26)) ltac:(lia) (FUZZ_NP_pos _)) as NPK.
    pose proof (Z.mul_nonneg_nonneg (4 - Z.of_nat c) (FUZZ_COST (2^26)) ltac:(lia) (FUZZ_COST_pos (2^26) ltac:(lia))) as FCK.
    pose proof CEIL' as CE. try rewrite alloc_ceiling_lit in CE.
    unfold AERRNO, ATP in ER.
    (* [comment removed for export] *)
    apply lrz_step_evt. unfold AINITFLAG.
    step. if_cases K'; zify_cond K'; [exfalso; rewrite ?unsigned_lit in K' by lia; lia|]. clear K'.
    do 4 step.
    eapply evt_cut.
    { eapply (memcpy_icpt_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m D S plen src junk' lo);
        rewrite ?unsigned_lit by lia;
        [ exact IC | exact MI | exact ST | exact CEIL' | unfold AINTRIN_STACK; lia | reflexivity | reflexivity | reflexivity
        | exact SRC | exact LSRC | exact BLK | lia | lia
        | exact (art_block_app_range AI _ _ _ _ _ _ _ _ _ A cap S plen HART ltac:(right; exact INA) ltac:(lia) ltac:(lia) ltac:(lia))
        | exact (art_block_app_range AI _ _ _ _ _ _ _ _ _ D plen D plen HART ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia))
        | apply wr_range_ok_high; lia
        | intros _; eapply shadow_ok_sub; [exact SOKo| lia| lia| lia] | intros _; exact SOKn | lia | lia ]. }
    intros msx nelH_; (nelim nelH_ 22%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m3 -> MU3 WM3 MI3 DST3 SRC3 ST3).
    replace (ret_pc (Z_to_bv 64 0x82200)) with (Z_to_bv 64 0x82200 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ?unsigned_lit in MU3, ST3 by lia.
    (* [comment removed for export] *)
    assert (WOK3 : Forall (cj_write_ok sp0 SPB ((D, plen) :: LB) []) [(D, D + plen); (bv_unsigned sp - 80 - AINTRIN_STACK, bv_unsigned sp - 80)]).
    { apply Forall_cons; [apply (cj_write_ok_block _ _ _ _ D plen); [left; reflexivity| lia| lia]|].
      apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit; unfold AINTRIN_STACK| rewrite SPBE]; lia| apply Forall_nil]. }
    assert (HA3 : ART sp0 SPB ((D, plen) :: LB) [] TRS B m3 mo g) by (eapply (art_frame AI); [exact HART| exact MU3| exact WM3| exact WOK3]).
    unfold AINTRIN_STACK in MU3.
    axport ER MU3 WM3 ER3. axport TFR MU3 WM3 TFR3. axport MFR MU3 WM3 MFR3. axport DS MU3 WM3 DS3. axport DIC MU3 WM3 DIC3.
    axport SEF MU3 WM3 SEF3. axport SIF MU3 WM3 SIF3. axport SSZ MU3 WM3 SSZ3. axport SOF MU3 WM3 SOF3.
    (* [comment removed for export] *)
    do 2 step. apply evt_done.
    change (Z_to_bv 64 6146256) with (Z_to_bv 64 AINITFLAG : word).
    eapply (trun_rounds AI TI S_LIB TROK LIBOK FUZZ SO_EMIT1 SO_EMIT2 sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11
              A cap D plen D src TP LO GT SPH SPBE SPAL ltac:(lia) BOT ltac:(right; split; [reflexivity| exact NE]) c ((D, plen) :: LB) TRS B 0 fc m3 mo g F KT);
      [| exact Hc| exact HK| exact KB].
    split; [exact HA3|]. split; [right; exact INA|]. split; [right; left; reflexivity|]. split.
    { right. split; [left; reflexivity|]. split; [exact (proj1 (rw_cells_CB_bytes _ _ _ _ DST3))| exact LSRC]. }
    split; [exact HT|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exists e; exact ER3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists u; exact TFR3|]. split; [exact MFR3|].
    split; [exact DS3|]. split; [exact DIC3|]. split; [exact SEF3|]. split; [exact SIF3|]. split; [exact SSZ3|]. split; [exact SOF3|]. split; [exact DM| exact FRM].
  Qed.
  (* [comment removed for export] *)
  Lemma trun_alloc : forall (c : nat) LB TRS B (F : bvmap 5 word) fc m mo g (junk data : list byte) (cl : Z) (KT : TSet) (u : list byte) (e : word)
      rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31,
    let len := zlength data in
    let plen := len - 6 - cl in
    ART sp0 SPB LB [] TRS B m mo g -> In (A, cap) LB -> TINV TI 0 TRS -> 4 * FUZZ_NP (2^26) <= NPMAX TI -> DRV_B_TRUN <= B ->
    ADRV 1 m mo g ->
    rw_cells asegs m A [CB (Z.to_nat len) data; CB (Z.to_nat (cap - len)) junk] ->
    0 <= cl < 32768 -> 6 + cl <= len -> len < 2^26 -> len <= cap -> plen <> 0 ->
    rw_cells asegs m AERRNO [C4 e] -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp - 80) -> TFRAME m u -> MFRAME m ->
    ADSTAT tid m -> DICPT m -> stderr_wfile0 m -> stdin_file m -> stack_shadow_zero m -> stdout_file m stdout_init ->
    DMOD fs FDS0 mo -> frm0 fc ->
    (1 <= c <= 4)%nat -> KT [] ->
    (forall ms' mo' g', TRET 0 (so_after (c - 1)) ms' mo' g' -> LRZ asegs ms' mo' g' KT) ->
    LRZ asegs (EST 0x821e4 F fc m rav x5 x6 x7 plen (Z_to_bv 64 (A + 6 + cl)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z.of_nat c) x28 x29 x30 x31) mo g
        (t_emit (W 1 emit_line) KT).
  Proof.
    intros until x31. intros len plen HART INA HT NPOK HB HDRV BUF CL CL6 LEN2 LENC PNZ ER MI ST TFR MFR DS DIC SEF SIF SSZ SOF DM FRM Hc HK KB.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART INA) 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    assert (PL : 0 < plen < 2^26) by (subst plen len; unfold zlength in *; lia).
    pose proof (cost_malloc_trun plen ltac:(lia)) as CM. pose proof (FUZZ_COST_pos (2^26) ltac:(lia)) as FC0. pose proof cost_free_eq as CF.
    assert (HBF : DRV_BFLOOR <= B) by (assert (DRVB : DRV_B_TRUN = 515669262528) by (vm_compute; reflexivity); unfold DRV_BFLOOR; rewrite DRVB in HB; lia).
    unfold DRV_B_TRUN in HB.
    assert (LSRC : Z.of_nat (length (skipn (Z.to_nat (6 + cl)) data)) = plen) by (rewrite length_skipn; subst plen len; unfold zlength in *; lia).
    (* [comment removed for export] *)
    assert (SRCP : forall LF SP m2, cj_pres sp0 LB LF SP m m2 -> bytes_at asegs m2 (A + 6 + cl) (skipn (Z.to_nat (6 + cl)) data)).
    { intros LF SP m2 PR.
      assert (B1 : rw_cells asegs m2 A [CB (Z.to_nat len) data]).
      { eapply cj_pres_rw_cells; [exact PR| exact (proj1 (proj1 (rw_cells_app m A [CB (Z.to_nat len) data] _) BUF))|].
        do 3 right; left. exists A, cap. split; [exact INA| cbn; subst len; unfold zlength in *; lia]. }
      pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ B1)) as BYA.
      rewrite <- (firstn_skipn (Z.to_nat (6 + cl)) data) in BYA. apply bytes_at_app in BYA. destruct BYA as [_ SRC].
      rewrite length_firstn in SRC. replace (A + Z.of_nat (Z.to_nat (6 + cl) `min` length data)) with (A + 6 + cl) in SRC by (subst len; unfold zlength in *; lia).
      exact SRC. }
    unfold AERRNO, ATP in ER. pose proof CEIL' as CE. try rewrite alloc_ceiling_lit in CE.
    apply lrz_step_evt. unfold AINITFLAG. do 2 step. apply evt_done.
    change (Z_to_bv 64 6146256) with (Z_to_bv 64 AINITFLAG : word).
    eapply (drv_malloc_nn AI TI TROK DI 0%nat) with (lo := lo) (np := 0) (n := plen) (sp0 := sp0) (errv := e);
      [ exact HART | exact HDRV | exact HT | unfold S_DRIVER; rewrite unsigned_lit by lia; cbn; tauto
      | rewrite !unsigned_lit by lia; lia | rewrite unsigned_lit by lia; rewrite SPBE; lia
      | rewrite unsigned_lit by lia; exact ST | exact CEIL' | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
      | unfold AERRNO, ATP; exact ER | exact MI | exact TP | reflexivity | unfold DRV_REQ_MAX; lia | lia | exact HBF | intros _; reflexivity | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 g2 errv2 TRS2 D junk' MI2 ST2 ER2 PR GM HT2 HV NZ BR' NIN HA2 HD2 BLK'.
    rewrite ?unsigned_lit in ST2, PR by lia.
    replace (ret_pc (Z_to_bv 64 0x821ec)) with (Z_to_bv 64 0x821ec : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply trun_copy with (u := u);
      [ exact HA2 | exact INA | exact NIN | exact HT2 | exact NPOK | lia | exact BLK' | exact (SRCP _ _ _ PR) | exact LSRC
      | lia | subst plen len; lia | exact PL | unfold AERRNO, ATP; exact ER2 | exact MI2 | exact ST2
      | eapply cj_pres_rw_cells; [exact PR| exact TFR| left; cbn; lia]
      | eapply cj_pres_rw_cells; [exact PR| exact MFR| left; unfold mframe; cbn; lia]
      | eapply ADSTAT_cj_pres; [exact DS| exact PR] | eapply DICPT_cj_pres; [exact DIC| exact PR]
      | eapply stderr_wfile0_cj_pres; [exact SEF| exact PR] | eapply stdin_file_cj_pres; [exact SIF| exact PR]
      | eapply stack_shadow_zero_cj_pres; [exact SSZ| exact PR| exact (art_lowshadow AI _ _ _ _ _ _ _ _ _ HA2)] | eapply stdout_file_cj_pres; [exact SOF| exact PR]
      | eapply DMOD_vm_only; [exact DM| exact HV] | exact FRM | exact Hc | exact HK | exact KB ].
  Qed.
  (* [comment removed for export] *)
  Theorem trun_main : trun_stmt AI DI TI sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap.
  Proof.
    intros t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc m mo g TRS B junk data cl e KT len plen.
    intros HART HT HB NPOK HDRV BUF SOK CL CL6 LEN2 LENC DM FRM ST MI ER IFL DS DIC SOF SEF SIF SSZ MFR HK KB.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART ltac:(left; reflexivity)) 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1.
    assert (PL : 0 <= plen < 2^26) by (subst plen len; unfold zlength in *; lia).
    assert (HB4 : 4 * FUZZ_COST (2^26) + 2 * cost_free <= B).
    { unfold DRV_B_TRUN in HB. pose proof (cost_malloc_pos (2^26) ltac:(lia)). lia. }
    unfold wz, ATRUN in *. unfold AERRNO, ATP in ER.
    (* [comment removed for export] *)
    destruct (ADSTAT_phase1 tid m DS IFL) as [AT1 (cdt & thr & sec & tm1 & LIBC)].
    destruct AT1 as ((f1 & f2 & f3 & pad & j1 & AX) & (j2 & AX1) & IC).
    unfold A_ATEXIT, atex_cells in AX. cbn [List.app] in AX. unfold A_ATEXIT in AX1. unfold A_LIBC in LIBC. unfold AINCB in IC.
    unfold AINITFLAG in IFL.
    (nelimp DS 17%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G1 _). unfold wz, AGOT_STDERR, ASTDERR_VAR in G1. revert G1. exit_lits. intros G1.
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (AINITFLAG, AINITFLAG + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM. unfold AINITFLAG in MU.
    pose proof CEIL' as CE. try rewrite alloc_ceiling_lit in CE.
    apply lrz_step_evt.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    step. step; fix_litstore; mem_after_store_opt. do 16 step. if_lit.
    do 2 step. fix_litstore; mem_after_store_opt.
    replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in * by lia.
    (* [comment removed for export] *)
    do 3 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (WOK : Forall (cj_write_ok sp0 SPB [(A, cap)] []) [(bv_unsigned sp - 80, bv_unsigned sp); (6146256, 6146256 + 1)])
      by (apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit| rewrite SPBE]; lia|];
          apply Forall_cons; [apply cj_write_ok_img; unfold ADATA_LO, AIMG_HI; lia| apply Forall_nil]).
    assert (HART1 : ART sp0 SPB [(A, cap)] [] TRS B m1 mo g) by (eapply (art_frame AI); [exact HART| exact MU| exact WM| exact WOK]).
    assert (HDRV1 : ADRV 1 m1 mo g) by (eapply (adrv_frame AI DI); [exact HART| exact HDRV| exact MU| exact WM| exact WOK]).
    assert (ADLITS : forall a, adstat_addr a -> ~ atex_addr a -> ADATA_LO <= a < AIMG_HI /\ a <> AINITFLAG).
    { intros a Hd Hx. revert Hd Hx. unfold adstat_addr, atex_addr, A_ATEXIT, A_AEF_INIT, AINCB, AINITFLAG, ATIDCELL, AOFL_HEAD, ASTDIN_USED, ASTDOUT_USED, ASTDERR_USED,
        AGOT_STDERR, ASTDERR_VAR, AGOT_GUARD, AGUARD, ATP, ADATA_LO, AIMG_HI; clear; intros; lia. }
    unfold ADATA_LO, AIMG_HI, AINITFLAG in ADLITS.
    assert (AG1 : magree (fun a => adstat_addr a /\ ~ atex_addr a) m m1).
    { eapply magree_of_munch; [exact MU| exact WM|]. intros a _ [Hd Hx]. pose proof (ADLITS a Hd Hx) as L. revert L. clear - CE LO. cbn. intros; lia. }
    axport DIC MU WM DIC1; axport SOF MU WM SOF1; axport SEF MU WM SEF1; axport SIF MU WM SIF1; axport SSZ MU WM SSZ1.
    clear MU WM WOK.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (atexit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo A_AEF_GUARD f1 f2 f3 pad j1 j2 cdt thr sec tm1);
        rewrite ?unsigned_lit by lia;
        [ exact ST | exact CEIL' | unfold ATEXIT_STACK; lia | lia | unfold A_AEF_GUARD; reflexivity | unfold A_AEF_GUARD; lia
        | unfold A_ATEXIT, atex_cells; cbn [List.app]; exact AX | unfold A_ATEXIT; exact AX1 | unfold A_LIBC; exact LIBC | exact MI ]. }
    intros msx nelH_; (nelim nelH_ 22%nat; intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 -> MU2 WM2 MI2 ST2 (g1 & g2 & g3 & pad2 & AX2) AXG).
    replace (ret_pc (Z_to_bv 64 0x8221c)) with (Z_to_bv 64 0x8221c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ?unsigned_lit in MU2, ST2 by lia. unfold ATEXIT_STACK, A_ATEXIT in MU2.
    (* [comment removed for export] *)
    assert (WOK2 : Forall (cj_write_ok sp0 SPB [(A, cap)] []) [(bv_unsigned sp - 80 - 48, bv_unsigned sp - 80); (A_ATEXIT + 8, A_ATEXIT + 12); (A_ATEXIT + 40, A_ATEXIT + 48); (A_ATEXIT + 296, A_ATEXIT + 304)]).
    { unfold A_ATEXIT. apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit| rewrite SPBE]; lia|].
      repeat (apply Forall_cons; [apply cj_write_ok_img; unfold ADATA_LO, AIMG_HI; cbn; lia|]). apply Forall_nil. }
    unfold A_ATEXIT in WOK2.
    assert (HART2 : ART sp0 SPB [(A, cap)] [] TRS B m2 mo g) by (eapply (art_frame AI); [exact HART1| exact MU2| exact WM2| exact WOK2]).
    assert (HDRV2 : ADRV 1 m2 mo g) by (eapply (adrv_frame AI DI); [exact HART1| exact HDRV1| exact MU2| exact WM2| exact WOK2]).
    axport IC MU2 WM2 IC2. axport IFL MU2 WM2 IFL2. axport G1 MU2 WM2 G2. axport FR MU2 WM2 TFR2. axport MFR MU2 WM2 MFR2. axport ER MU2 WM2 ER2. axport BUF MU2 WM2 BUF2.
    axport DIC1 MU2 WM2 DIC2; axport SOF1 MU2 WM2 SOF2; axport SEF1 MU2 WM2 SEF2; axport SIF1 MU2 WM2 SIF2; axport SSZ1 MU2 WM2 SSZ2.
    assert (DS2 : ADSTAT tid m2).
    { eapply (ADSTAT_phase2 tid m m2 DS).
      - eapply magree_trans; [exact AG1|]. eapply magree_of_munch; [exact MU2| exact WM2|]. intros a _ [Hd Hx].
        pose proof (ADLITS a Hd Hx) as L. revert L Hx. unfold atex_addr, A_ATEXIT, A_AEF_INIT, AINCB. clear - CE LO. cbn. intros; lia.
      - split; [exists g1, g2, g3, pad2; exact AX2|]. split; [exact AXG|]. split; [unfold A_AEF_INIT; exact IFL2| unfold AINCB; exact IC2]. }
    clear DS DIC SOF SEF SIF SSZ HART HDRV HART1 HDRV1 AG1 AX AX1 LIBC IC G1 DIC1 SOF1 SEF1 SIF1 SSZ1 MFR FR IFL WOK2 AX2 AXG MU2 WM2 BUF.
    (* [comment removed for export] *)
    step. if_lit. do 2 step. step. if_lit.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - (* [comment removed for export] *)
      assert (K0 : cl = 0) by lia. rewrite K0, tcalls_zero in KB.
      do 2 step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + (* [comment removed for export] *)
        apply evt_done.
        change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)). change (Z_to_bv 64 6146256) with (Z_to_bv 64 AINITFLAG : word).
        subst plen. rewrite K0. replace (A + 6 + 0) with (A + 6 + cl) by lia. replace (len - 6 - 0) with (len - 6 - cl) by lia.
        eapply (trun_alloc 1%nat); first [exact HART2| exact HT| exact NPOK| exact HB| exact HDRV2| exact BUF2| exact DM| exact FRM| exact ST2| exact MI2| exact DS2| exact DIC2| exact SOF2| exact SEF2| exact SIF2| exact SSZ2
                                          | exact MFR2| exact TFR2| exact HK| exact KB| left; reflexivity| unfold AERRNO, ATP; exact ER2| lia].
      + (* [comment removed for export] *)
        apply evt_done.
        rewrite K2. change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)). change (Z_to_bv 64 6146256) with (Z_to_bv 64 AINITFLAG : word).
        eapply (trun_empty 1%nat); [| exact HB4| lia| exact HK| exact KB].
        split; [exact HART2|]. split; [left; reflexivity|]. split; [exact HT|]. split; [exact NPOK|]. split; [exists e; unfold AERRNO, ATP; exact ER2|].
        split; [exact MI2|]. split; [exact ST2|]. split; [eexists; exact TFR2|]. split; [exact MFR2|].
        split; [exact DS2|]. split; [exact DIC2|]. split; [exact SEF2|]. split; [exact SIF2|]. split; [exact SSZ2|]. split; [exact SOF2|]. split; [exact DM| exact FRM].
    - (* [comment removed for export] *)
      pose proof (proj1 (rw_cells_CB_bytes _ _ _ _ (proj1 (proj1 (rw_cells_app _ A [CB (Z.to_nat len) data] _) BUF2)))) as BYA.
      destruct (nth_error data 2) as [b2|] eqn:Hb2. 2:{ exfalso. apply nth_error_None in Hb2. subst len; unfold zlength in *; lia. }
      pose proof (u8ro_read asegs _ A data 2 b2 _ BYA Hb2 ltac:(lia) eq_refl) as RD2.
      pose proof (bv_unsigned_in_range 8 b2) as Rb2. change (bv_modulus 8) with 256 in Rb2.
      destruct (tcalls_pos cl data b2 ltac:(lia) Hb2) as [TC TCB].
      do 3 step. unfold zxb. rewrite (unsigned_lit (bv_unsigned b2)) by lia. rewrite TC.
      change (Z_to_bv 64 6146256) with (Z_to_bv 64 AINITFLAG : word).
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + (* [comment removed for export] *)
        apply evt_done. rewrite K2.
        eapply (trun_empty (tcalls cl data)); [| exact HB4| exact TCB| exact HK| exact KB].
        split; [exact HART2|]. split; [left; reflexivity|]. split; [exact HT|]. split; [exact NPOK|]. split; [exists e; unfold AERRNO, ATP; exact ER2|].
        split; [exact MI2|]. split; [exact ST2|]. split; [eexists; exact TFR2|]. split; [exact MFR2|].
        split; [exact DS2|]. split; [exact DIC2|]. split; [exact SEF2|]. split; [exact SIF2|]. split; [exact SSZ2|]. split; [exact SOF2|]. split; [exact DM| exact FRM].
      + (* [comment removed for export] *)
        apply evt_done.
        eapply (trun_alloc (tcalls cl data)); first [exact HART2| exact HT| exact NPOK| exact HB| exact HDRV2| exact BUF2| exact DM| exact FRM| exact ST2| exact MI2| exact DS2| exact DIC2| exact SOF2| exact SEF2| exact SIF2| exact SSZ2
                                          | exact MFR2| exact TFR2| exact HK| exact KB| exact TCB| left; reflexivity| unfold AERRNO, ATP; exact ER2| lia].
  Qed.
End S.

(* [comment removed for export] *)
Theorem trun_proof (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface) (S_LIB : list (list Z)) :
  drv_traces_ok TI -> (forall tr, In tr S_LIB -> STAT TI tr) -> llvmfuzz_stmt AI TI S_LIB ->
  so_emit_first_stmt -> so_emit_again_stmt ->
  forall sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap,
    trun_side sp tp lo SPB -> trun_stmt AI DI TI sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap.
Proof.
  intros TROK LIBOK FZ SE1 SE2. intros until cap. intros nelH_; (nelim nelH_ 8%nat; intros TP LO GT SPH SPBE SPAL WIN BOT).
  eapply trun_main; eassumption.
Qed.


End CeilWrap.
End Drv_trun.

(* [comment removed for export] *)
Module Drv_main.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_hooks OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.Drv_art Drv_usage Drv_open Drv_loop Drv_hdr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA Drv_trun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.

Section Leaves.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface) (S_LIB : list (list Z)).
  (* [comment removed for export] *)
  Hypothesis TROK : drv_traces_ok TI.
  Hypothesis LIBOK : forall tr, In tr S_LIB -> STAT TI tr.
  Hypothesis NPOK : 4 * FUZZ_NP (2^26) <= NPMAX TI.
  (* [comment removed for export] *)
  Hypothesis FUZZ : llvmfuzz_stmt AI TI S_LIB.
  (* [comment removed for export] *)
  Hypothesis SO_EXIT : so_exit_stmt.
  Hypothesis SO_REFUSED : so_diag_refused_stmt.
  Hypothesis SO_READERR : so_diag_read_error_stmt.
  Hypothesis SO_CANTOPEN : so_diag_cannot_open_stmt.
  Hypothesis SO_SHORT : so_diag_short_stmt.
  Hypothesis SO_OVERRUN : so_diag_overrun_stmt.
  Hypothesis SO_EMIT1 : so_emit_first_stmt.
  Hypothesis SO_EMIT2 : so_emit_again_stmt.
  Hypothesis SO_USAGE : so_diag_usage_stmt.

  Theorem trun_all_ok : trun_all AI DI TI.
  Proof. unfold trun_all. intros. eapply (trun_proof AI DI TI S_LIB); eassumption. Qed.

  Theorem main_two_ok : main_two_stmt AI DI TI.
  Proof.
    eapply (main_two_proof AI DI TI); try eassumption; try exact argv_client.
    intros. eapply (loop_proof AI DI TI); try eassumption.
    eapply (post_proof AI DI TI); try eassumption. exact trun_all_ok.
  Qed.

  Theorem main_usage_ok : main_usage_stmt AI TI.
  Proof. eapply (main_usage AI TI); eassumption. Qed.
End Leaves.
End CeilWrap.
End Drv_main.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface CJ_tree AShadow CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Exit SO_base Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_trunA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_trunA.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_base Drv_icpt_defs Drv_dicpt Drv_iface2 Drv_traces CJ_fuzz_iface Drv_stmt.
Import Drv_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Definition argv_str_at (m : word -> option byte) (sp : Z) (i : nat) (s : list byte) : Prop :=
  exists (P : Z) (slack : list byte),
    rw_cells asegs m (sp + 56 + 8 * Z.of_nat i) [C8 (wz P)]
    /\ bytes_at asegs m P (s ++ Z_to_bv 8 0 :: slack)
    /\ (- (P + zlength s + 1)) mod 8 <= zlength slack
    /\ sp + 48 <= P /\ P + zlength s + 1 + zlength slack + 16 <= 2^47.

Section Top.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface).
  Let ART := CJ_iface.ART AI.
  Let ADRV := Drv_iface2.ADRV AI DI.

  Definition a_main_ready (argv : list (list byte)) (fs : Fs) (ms : machine_state) (mo : Model) (g : lghost) : Prop :=
    exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (tid errv : word) (B0 : Z),
      ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz AMAIN) fc None m (seg_rom asegs)
      /\ ra = wz ASTAGE2_RET /\ tp = wz ATP /\ a0 = wz (Z.of_nat (length argv)) /\ a1 = wz (bv_unsigned sp + 56) /\ frm0 fc
      (* [comment removed for export] *)
      /\ ART (bv_unsigned sp + 48) (bv_unsigned sp) [] [] [] B0 m mo g /\ DRV_B_MAIN <= B0 /\ ADRV DRV_CALLS m mo g
      (* [comment removed for export] *)
      /\ DMOD fs FDS0 mo
      /\ stk asegs m lo (bv_unsigned sp) /\ lo + 2^22 <= bv_unsigned sp /\ alloc_ceiling <= lo /\ bv_unsigned sp + 48 <= 2^47
      /\ sp_window_lo <= bv_unsigned sp + 48 /\ bv_unsigned sp mod 16 = 0 /\ ASTACK_BOTTOM (bv_unsigned sp + 48) <= lo
      /\ mem_inv asegs m
      /\ ADSTAT tid m /\ 0 < bv_unsigned tid < 2^22 /\ DICPT m
      /\ rw_cells asegs m AERRNO [C4 errv] /\ rw_cells asegs m AINITFLAG [C1 (Z_to_bv 8 0)]
      /\ stdout_file m stdout_init /\ stderr_wfile0 m /\ stdin_file m /\ stack_shadow_zero m
      /\ (exists stj, rw_cells asegs m ARS [CB RSN stj])
      /\ argv_str_at m (bv_unsigned sp) 0 (hd [] argv)
      /\ (length argv = 2%nat -> argv_str_at m (bv_unsigned sp) 1 (nth 1 argv [])).

  (* [comment removed for export] *)
  Definition a_main_stmt04 : Prop :=
    forall (argv : list (list byte)) (fs : Fs) (ms : machine_state) (mo : Model) (g : lghost),
      valid_argv argv -> a_main_ready argv fs ms mo g -> LRZ asegs ms mo g (spec04 argv fs).

  (* [comment removed for export] *)
  Hypothesis TI0 : TINV TI 0 [].
  Hypothesis TROK : drv_traces_ok TI.
  Hypothesis MAIN2 : main_two_stmt AI DI TI.
  Hypothesis USAGE : main_usage_stmt AI TI.

  Theorem a_main_of_trunk : a_main_stmt04.
  Proof.
    intros argv fs ms mo g VA RDY.
    destruct RDY as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11
                     & t3 & t4 & t5 & t6 & F & fc & m & lo & tid & errv & B0
                     & -> & RA & TP & A0 & A1 & FRM & HART & HB0 & HDRV & DM & ST & LO & CEIL & SPH & WIN & SPAL & BOT & MI & DS & TID & DIC & ER & IFL
                     & SOF & SEF & SIF & SSZ & RSC & AV0 & AV1).
    pose proof VA as (VLEN & _ & VL & VN & VTL).
    unfold spec04.
    assert (US : forall argv0, hd [] argv = argv0 -> length argv <> 2%nat -> spec argv fs = t_die (msg_usage argv0) fs ->
                 LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz AMAIN) fc None m (seg_rom asegs)) mo g (spec argv fs)).
    { intros argv0 H0 HN ->. destruct AV0 as (P0 & slack & CELL & BY & SLK & PLO & PHI). rewrite H0 in BY, SLK, PHI.
      replace (bv_unsigned sp + 56 + 8 * Z.of_nat 0) with (bv_unsigned sp + 56) in CELL by lia.
      eapply USAGE with (lo := lo) (argc := Z.of_nat (length argv)) (P0 := P0) (argv0 := argv0) (slack := slack) (tid := tid) (B0 := B0);
        first [ exact DM | exact HART | exact TI0 | exact TROK | exact RA | exact TP | exact A0 | exact A1 | exact ST | exact LO | exact CEIL | exact SPH | exact SPAL
              | exact MI | exact FRM | exact DS | exact TID | exact DIC | exact SOF | exact SEF | exact SIF | exact SSZ | exact CELL | exact BY | exact SLK | exact PLO | exact PHI
              | (clear - VLEN HN; lia)
              | (destruct argv as [|x rest]; [cbn in VLEN; clear - VLEN; lia|]; cbn [hd] in H0; subst x;
                 first [ exact (Forall_inv VN) | pose proof (Forall_inv VL) as HL; cbn beta in HL; clear - HL; unfold zlength; lia ]) ]. }
    destruct argv as [|argv0 [|path [|x rest]]].
    - exfalso. cbn in VLEN. lia.
    - apply (US argv0); [reflexivity| cbn; lia| reflexivity].
    - (* [comment removed for export] *)
      clear US. destruct (AV1 eq_refl) as (P1 & slack & CELL & BY & SLK & PLO & PHI). cbn [nth] in BY, SLK, PHI.
      replace (bv_unsigned sp + 56 + 8 * Z.of_nat 1) with (bv_unsigned sp + 64) in CELL by lia.
      cbn [tl] in VTL. apply Forall_cons_iff in VTL as [[HSL HDDb] _].
      assert (HDD : path <> dotdot_path).
      { intros E. rewrite E in HDDb. rewrite (proj2 (path_eqb_eq dotdot_path dotdot_path) eq_refl) in HDDb. discriminate. }
      rewrite spec_two.
      (* [comment removed for export] *)
      eapply MAIN2 with (lo := lo) (P1 := P1) (slack := slack) (tid := tid) (errv := errv) (B0 := B0);
        [ exact DM | exact HART | exact HB0 | exact HDRV | exact TI0 | exact TROK | exact RA | exact TP | exact A0 | exact A1 | exact ST | exact LO | exact CEIL | exact SPH
        | exact WIN | exact SPAL | exact BOT | exact MI | exact FRM | exact DS | exact TID | exact DIC | exact ER | exact IFL | exact SOF | exact SEF | exact SIF | exact SSZ
        | exact RSC | exact CELL | exact BY
        | exact (Forall_inv (Forall_inv_tail VN)) | exact HSL | exact HDD | exact SLK
        | pose proof (Forall_inv (Forall_inv_tail VL)) as HL; cbn beta in HL; clear - HL; unfold zlength; lia
        | exact PLO | exact PHI ].
    - apply (US argv0); [reflexivity| cbn; lia| reflexivity].
  Qed.
End Top.

(* [comment removed for export] *)
Theorem a_main_proof04 : forall (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface) (S_LIB : list (list Z)),
  TINV TI 0 [] -> drv_traces_ok TI -> (forall tr, In tr S_LIB -> STAT TI tr) -> 4 * FUZZ_NP (2^26) <= NPMAX TI ->
  llvmfuzz_stmt AI TI S_LIB ->
  so_exit_stmt -> so_diag_refused_stmt -> so_diag_read_error_stmt -> so_diag_cannot_open_stmt ->
  so_diag_short_stmt -> so_diag_overrun_stmt -> so_emit_first_stmt -> so_emit_again_stmt -> so_diag_usage_stmt ->
  a_main_stmt04 AI DI.
Proof.
  intros AI DI TI S_LIB TI0 TROK LIBOK NPOK FUZZ SE SR SRD SC SS SV E1 E2 SU.
  apply (a_main_of_trunk AI DI TI); [exact TI0| exact TROK| |].
  - eapply (main_two_ok AI DI TI S_LIB); eassumption.
  - eapply (main_usage_ok AI TI); eassumption.
Qed.
End CeilWrap.
