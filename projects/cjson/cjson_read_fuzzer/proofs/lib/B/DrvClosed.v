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
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RegsEquiv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require SO_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Exit_pre2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require SO_piface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require SO_stdio_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_trunA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
Module SO_exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.Startup_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.LRzAt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Stdio_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit_pre2.Exit_pre1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit_pre2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_piface.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_rz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_stdio_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_trunA.SO_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).
Local Notation lrzt := (LSO_rz.lrzt bsegs).
Local Notation LRZ := (LRz.LRZ bsegs).
Local Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutModel.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.

  (* [comment removed for export] *)

  Lemma lrzt_rd_so : forall st mo g (R : stdout_st * stdout_st -> Prop), R (st, st) -> lrzt (rd_so get_so st) mo g [] R.
  Proof.
    intros st mo g R HR. unfold rd_so. eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (st, st))); [apply lrzt_mget; reflexivity|].
    intros a s' E. injection E as -> ->. apply lrzt_mret. exact HR.
  Qed.

  Lemma lrzt_upd_so : forall f st mo g (R : unit * stdout_st -> Prop), R (tt, f st) -> lrzt (upd_so get_so set_so f st) mo g [] R.
  Proof. intros f st mo g R HR. unfold upd_so. apply lrzt_mupd. exact HR. Qed.

  Lemma lrzt_stdout_stdio_write : forall s st mo g,
    chan_ok mo 1 -> zlength (so_buf st) + zlength s <= 67108864 ->
    lrzt (stdout_stdio_write get_so set_so s st) mo g (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st ++ s)))
        (fun r => snd r = mkStdout true [] (so_lbf_nl st) (so_first st)).
  Proof.
    intros s st mo g CH B. unfold stdout_stdio_write.
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (st, st))); [apply lrzt_rd_so; reflexivity|]. intros so s' E. injection E as -> ->.
    eapply lrzt_mbind_nil_r; [apply (lrzt_stdio_writev bsegs st mo g 1 (so_buf st) s CH); exact B|].
    intros [] s' E. cbn [snd] in E. subst s'. apply lrzt_upd_so. reflexivity.
  Qed.

  Lemma lrzt_stdout_writefn : forall s st mo g,
    chan_ok mo 1 -> zlength (so_buf st) + zlength s <= 67108864 ->
    lrzt (stdout_writefn get_so set_so s st) mo g (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st ++ s)))
        (fun r => snd r = mkStdout true [] (if so_first st then false else so_lbf_nl st) false).
  Proof.
    intros s st mo g CH B. unfold stdout_writefn.
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (st, st))); [apply lrzt_rd_so; reflexivity|]. intros so s' E. injection E as -> ->.
    destruct st as [act buf lbf first]. cbn [so_first so_buf so_lbf_nl] in *. destruct first.
    - eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => snd r = mkStdout act buf false false)).
      + eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (tt, mkStdout act buf lbf false))); [apply lrzt_upd_so; reflexivity|].
        intros [] s1 E. injection E as ->.
        eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => (exists err, fst r = SErr err) /\ snd r = mkStdout act buf lbf false));
          [eapply (lrzt_ioctl bsegs); [exact CH| discriminate|]; intros err; split; [exists err; reflexivity| reflexivity] |].
        intros r s1 [[err E1] E2]. cbn [fst snd] in E1, E2. subst r s1. apply lrzt_upd_so. reflexivity.
      + intros [] s1 E. cbn [snd] in E. subst s1.
        eapply lrzt_mono; [apply lrzt_stdout_stdio_write; [exact CH| cbn [so_buf]; exact B]|]. intros [[] s2] E2. exact E2.
    - eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (tt, mkStdout act buf lbf false))); [apply lrzt_mret; reflexivity|].
      intros [] s1 E. injection E as ->.
      eapply lrzt_mono; [apply lrzt_stdout_stdio_write; [exact CH| cbn [so_buf]; exact B]|]. intros [[] s2] E2. exact E2.
  Qed.

  Lemma lrzt_stdout_exit_flush : forall st mo g,
    chan_ok mo 1 -> zlength (so_buf st) <= 67108864 ->
    lrzt (stdout_exit_flush get_so set_so st) mo g (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st))) (fun _ => True).
  Proof.
    intros st mo g CH B. unfold stdout_exit_flush.
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (st, st))); [apply lrzt_rd_so; reflexivity|]. intros so s' E. injection E as -> ->.
    destruct (Z.ltb_spec 0 (zlength (so_buf st))) as [P|N].
    - rewrite <- (app_nil_r (so_buf st)) at 1. eapply lrzt_mono; [apply lrzt_stdout_writefn; [exact CH| unfold zlength in *; cbn [length]; lia]|]. intros; exact I.
    - replace (so_buf st) with (@nil Z) by (symmetry; apply length_zero_iff_nil; unfold zlength in N; lia). cbn [to_bytes map]. apply lrzt_mret. exact I.
  Qed.
End StdoutModel.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitImpl.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.
  Local Open Scope bv_scope.

  Lemma exit_spec_so : forall (s : stdout_st) (Q : Empty_set -> stdout_st -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (code t : Z)
      (cdt thr sec : byte) (tm1 : word) (jA jB jC jD : list byte) (guard : word),
    stk bsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo + AEXIT_DEPTH <= bv_unsigned sp)%Z -> (bv_unsigned sp < 2^47)%Z ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 code -> (0 <= code < 256)%Z -> (0 < t < 2^22)%Z ->
    rw_cells bsegs m ATIDCELL [C4 (Z_to_bv 64 t)] ->
    rw_cells bsegs m 0x5fcbe0 [C4 (Z_to_bv 64 0)] ->
    ATEX m ->
    rw_cells bsegs m 0x5fcae0 [C8 (Z_to_bv 64 0x71944)] ->
    rw_cells bsegs m 0x5fcc00 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    fini_cells m ->
    rw_cells bsegs m 0xa6350 [C1 (Z_to_bv 8 0)] ->
    cells_at bsegs m 0x13b860 [C1 (Z_to_bv 8 0)] ->
    unreg_cells m -> unreg_cells2 m -> icpt_cells m -> poison_cells m ->
    (forall a, (AGLOBALS <= a < AGLOBALS + 704)%Z -> m (wa a) = None) ->
    rw_cells bsegs m 0xa6300 [C8 (Z_to_bv 64 1)] -> rw_cells bsegs m 0xa7270 [C8 (Z_to_bv 64 0)] ->
    rw_cells bsegs m 0x7fffc23c [CB 36 jA] -> rw_cells bsegs m 0x8000cb98 [CB 8 jB] ->
    rw_cells bsegs m 0x800b3808 [CB 4 jC] -> rw_cells bsegs m 0x8000cc04 [CB 88 jD] ->
    rw_cells bsegs m AOFL_HEAD [C8 z64] ->
    rw_cells bsegs m ASTDIN_USED [C8 (Z_to_bv 64 ASTDIN)] ->
    rw_cells bsegs m ASTDOUT_USED [C8 (Z_to_bv 64 ASTDOUT)] ->
    rw_cells bsegs m ASTDERR_USED [C8 (Z_to_bv 64 ASTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m -> stdin_file m ->
    rw_cells bsegs m AGOT_GUARD [C8 (Z_to_bv 64 AGUARD)] -> rw_cells bsegs m AGUARD [C8 guard] ->
    mem_inv bsegs m ->
    implM bsegs (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 AEXITF) fc None m (seg_rom bsegs)).
  Proof.
    intros until guard. intros ST CEIL LO SPH Htp Ha0 Hc Ht TIDC EXL ATX BA LIBC FC FIN PCG UC UC2 IC PC NONE REG MUT SHA SHB SHC SHD
           OFL SIN SOU SEU SOF SEF SIF GG GU MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold AEXIT_DEPTH, AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH in LO.
    unfold Driver.exit_model.
    eapply (implM_bind bsegs _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x8da04) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x8da04) fc None m' (seg_rom bsegs))).
    - change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      unfold implM. iprefix.
      eapply evt_cut.
      { exact (aexit_prefix_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc m lo code t cdt thr sec tm1 jA jB jC jD
                 ST ltac:(exact CEIL) LO SPH Htp Ha0 ltac:(lia) Ht TIDC EXL ATX BA LIBC PCG FC UC UC2 IC PC NONE FIN REG MUT SHA SHB SHC SHD MI). }
      intros ms1 PO. destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m1 & -> & MU & WM & MI1 & ST1 & FR1 & _).
      (* [comment removed for export] *)
      unfold AEXIT_PRE_DEPTH, FINI_DEPTH, UNREG_DEPTH in MU.
      Local Ltac carry H MU WM := eapply rw_cells_transport; [exact H | exact MU | exact WM | exit_lits; cbn; repeat split; lia].
      Local Ltac fw := exit_lits; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.
      pose proof (stdio_exit_proof get_so set_so (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)) as SE.
      unfold stdio_exit_spec_stmt, implM in SE.
      apply evt_done. eapply impl_epost_mono.
      { eapply (SE (Z_to_bv 64 0x8da04) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 ATP) u0 u1 u2 (Z_to_bv 64 code) s1
                    v0 v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 lo s guard cdt thr sec tm1);
          [ rewrite unsigned_lit by lia; exact ST1
          | carry LIBC MU WM | carry OFL MU WM | carry SIN MU WM | carry SOU MU WM | carry SEU MU WM
          | eapply stdout_file_munch; [exact SOF | exact MU | exact WM | fw]
          | eapply stderr_file_munch; [exact SEF | exact MU | exact WM | fw]
          | eapply stdin_file_munch; [exact SIF | exact MU | exact WM | fw]
          | carry GG MU WM | carry GU MU WM
          | exact MI1
          | rewrite unsigned_lit by lia; lia
          | exact CEIL ]. }
      intros [[] s'] ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO.
      destruct_exs PO. destruct PO as (E & PO). subst ms'. cbn [fst snd].
      replace (ret_pc (Z_to_bv 64 0x8da04)) with (Z_to_bv 64 0x8da04 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat eexists; cbv delta [mkR]; reflexivity.
    - intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implM_sys. do 4 lstep. step_ecall.
      split; [ at_node_red; split; [right; reflexivity | reflexivity] | intros rsp a H; cbn in H; discriminate H].
  Time Qed.
End ExitImpl.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem so_exit_proof : so_exit_stmt.
Proof.
  unfold so_exit_stmt. intros until guard.
  intros CH ST CEIL LO SPH Htp Ha0 Hc Ht TIDC EXL ATX BA LIBC FC FIN PCG UC UC2 IC PC NONE REG MUT SHA SHB SHC SHD
         OFL SIN SOU SEU SOF BND SEF SIF GG GU MI.
  pose proof (exit_spec_so so (fun _ _ _ => False) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo code t cdt thr sec tm1 jA jB jC jD guard
                ST CEIL LO SPH Htp Ha0 Hc Ht TIDC EXL ATX BA LIBC FC FIN PCG UC UC2 IC PC NONE REG MUT SHA SHB SHC SHD
                OFL SIN SOU SEU SOF SEF SIF GG GU MI) as H.
  unfold Driver.exit_model, implM, mbind in H. cbn [io_exit io_S] in H. apply impl_bind_inv in H.
  pose proof (lrzt_stdout_exit_flush so mo g CH ltac:(lia)) as RZ.
  unfold W. unfold t_exit.
  refine (RZ (fun a ms' => ITree.impl bsegs (at_node bsegs) (msys (NExit code) dec_exit (snd a)) (epost (fun (_ : Empty_set * stdout_st) (_ : machine_state) => False)) ms') _ _ _ (t_emit_has_nil _ _) _).
  - eapply impl_mono; [exact H|]. intros [|a] ms'; cbn [epost]; [intros _; exact I| intros X; exact X].
  - intros a ms' Hi _. unfold msys in Hi. fold (t_exit (Z_to_bv 64 code) (m_fs mo)).
    eapply (lrz_impl_enode bsegs); [exact Hi |]. intros ms1 Hat _. apply lrz_at_exit; [exact Hat | exact Hc].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
End SO_exit.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Image.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_pop_arg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_mlib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Printf_pieces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_str3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcleaf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcommon_tb.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcommon_su.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcommon_sco.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcommon_sre.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_fprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require SO_fprintf.
Module SO_diag.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_vfprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_pieces.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.ICPT_pcdefs2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcommon_tb OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcommon_su OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcommon_sco OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcommon_sre OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_base.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_fprintf.SO_printf_bridge OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_fprintf.SO_fwritex_stderr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_fprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_trunA.SO_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_piface.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.      (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM bsegs c s Q ms) | _ => idtac end.

Notation mem := (word -> option byte).
Local Notation LRZ := (LRz.LRZ bsegs).
Local Notation lrzt := (LSO_rz.lrzt bsegs).
Local Notation zbl := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib.zb.         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zlength_app' : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

(* [comment removed for export] *)

Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros; unfold to_bytes; apply map_app. Qed.
Lemma to_bytes_of_bytes : forall l : list byte, to_bytes (map bv_unsigned l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn. f_equal; [| exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_wrap, bv_modulus in *. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma lrzt_stderr_pieces : forall {St} (ps : list (list Z)) (buf : list Z) (st : St) mo g,
  chan_ok mo 2 -> Forall (fun p => zlength p <= 2^25) ps -> zlength buf <= INTERNAL_BUFSIZ ->
  exists e buf', buf ++ concat ps = e ++ buf' /\ zlength buf' <= INTERNAL_BUFSIZ /\
    lrzt (stderr_pieces buf ps st) mo g (map (WriteEv (Z_to_bv 64 2)) (to_bytes e)) (fun r => r = (buf', st)).
Proof.
  intros St ps. induction ps as [|p ps IH]; intros buf st mo g CH SM HB.
  - exists [], buf. cbn [concat]. rewrite app_nil_r. split; [reflexivity|]. split; [exact HB|].
    cbn [stderr_pieces to_bytes map]. apply lrzt_mret. reflexivity.
  - apply Forall_cons_iff in SM. destruct SM as [SP SM]. cbn [stderr_pieces concat].
    destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)) as [LT|GE].
    + destruct (IH [] st mo g CH SM ltac:(unfold INTERNAL_BUFSIZ, zlength; cbn; lia)) as (e2 & buf2 & E2 & HB2 & RZ2).
      exists ((buf ++ p) ++ e2), buf2. split; [cbn [app] in E2; rewrite E2, !app_assoc; reflexivity|]. split; [exact HB2|].
      rewrite to_bytes_app, map_app.
      eapply lrzt_mbind.
      * apply (lrzt_stdio_writev bsegs st mo g 2 buf p CH). unfold INTERNAL_BUFSIZ in *. lia.
      * intros [] s' Hs. cbn [snd] in Hs. subst s'. exact RZ2.
    + destruct (IH (buf ++ p) st mo g CH SM ltac:(rewrite zlength_app'; lia)) as (e2 & buf2 & E2 & HB2 & RZ2).
      exists e2, buf2. split; [rewrite <- E2, app_assoc; reflexivity|]. split; [exact HB2| exact RZ2].
Qed.

Lemma lrzt_stderr_fprintf : forall {St} (ps : list (list Z)) (st : St) mo g,
  chan_ok mo 2 -> Forall (fun p => zlength p <= 2^25) ps ->
  lrzt (stderr_fprintf ps st) mo g (map (WriteEv (Z_to_bv 64 2)) (to_bytes (concat ps))) (fun r => snd r = st).
Proof.
  intros St ps st mo g CH SM.
  destruct (lrzt_stderr_pieces ps [] st mo g CH SM ltac:(unfold INTERNAL_BUFSIZ, zlength; cbn; lia)) as (e & buf' & E & HB & RZ).
  cbn [app] in E. rewrite E, to_bytes_app, map_app. unfold stderr_fprintf.
  eapply lrzt_mbind; [exact RZ|]. intros b s' Hs. injection Hs as -> ->.
  replace (to_bytes buf') with (to_bytes (buf' ++ [])) by (rewrite app_nil_r; reflexivity).
  apply (lrzt_stdio_writev bsegs st mo g 2 buf' [] CH).
 unfold INTERNAL_BUFSIZ, zlength in *. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FPRINTI_DEPTH : Z := 112 + VF_DEPTH.
Lemma FPRINTI_DEPTH_le : FPRINTI_DEPTH <= AFPRINTF_STACK.
Proof. unfold FPRINTI_DEPTH, AFPRINTF_STACK, VF_DEPTH. lia. Qed.

Lemma fmt_cells_munch_stack : forall u v m m', fmt_cells m -> munch [(u, v)] m m' -> alloc_ceiling <= u -> fmt_cells m'.
Proof.
  intros u v m m' H MU Hu. try rewrite alloc_ceiling_lit in Hu.
  destruct H as (IC & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  split; [eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil]|].
  repeat match goal with |- _ /\ _ => split end;
    (eapply ro_cells_transport; [eassumption| exact MU| cbn; lia]).
Qed.
Lemma fmt_vfi : forall m, fmt_cells m -> vfi_cells m.
Proof. intros m (IC & CF & _ & _ & RVF & _). exact (conj IC (conj CF RVF)). Qed.

Lemma stderr_wfile_stk : forall m m' lo hi, stderr_wfile m -> munch [(lo, hi)] m m' -> wmono bsegs m m' -> 0x5ff000 <= lo -> stderr_wfile m'.
Proof.
  intros m m' lo hi SF MU WM Hlo. unfold stderr_wfile in *. exit_lits. destruct SF as (flags & mode & e & wend & tail & FC & FL).
  exists flags, mode, e, wend, tail. split; [| exact FL].
  eapply rw_cells_transport; [exact FC | exact MU | exact WM | cbn [disjoint_from cells_size file_cells file_cells_r AF_STDIO_CLOSE AF_STDIO_SEEK csize Nat.add]; lia].
Qed.

Lemma bytes_Forall_pos : forall s : list byte, ~ In (Z_to_bv 8 0) s -> Forall (fun c => 0 < c < 256) (map bv_unsigned s).
Proof.
  intros s NI. apply Forall_forall. intros c Hc. apply in_map_iff in Hc. destruct Hc as (b & <- & Hb).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE]; [|lia].
  exfalso. apply NI. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite E. reflexivity.
Qed.
Lemma zb_of_bytes : forall s : list byte, zbl (map bv_unsigned s) = s.
Proof. intros s. change (zbl (map bv_unsigned s)) with (to_bytes (map bv_unsigned s)). apply to_bytes_of_bytes. Qed.
Lemma zlength_map' : forall {A B} (f : A -> B) l, zlength (map f l) = zlength l.
Proof. intros. unfold zlength. rewrite length_map. reflexivity. Qed.

Section Fprinti.
  Context {St : Type}.

  Definition fprinti_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : St -> machine_state -> Prop :=
    fun st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (ASTDERR, ASTDERR + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stderr_wfile m'
      /\ assp_cells m' canary.

  (* [comment removed for export] *)
  Lemma fprinti_s :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (fa : Z) (fmt : list Z) (str slack : list byte) (ps : list (list Z)) (r : Z)
           (lo : Z) (canary : word),
      pcommon_s_stmt fa ->
      a0 = Z_to_bv 64 ASTDERR -> a1 = Z_to_bv 64 fa ->
      stderr_wfile m -> fmt_cells m -> MRT m -> lowsh_at m ->
      bytes_at bsegs m fa (zbl fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
      printf_pieces fmt [PA_s (map bv_unsigned str)] = Some (ps, r) -> fp_calls (length fmt) fmt [PA_s (map bv_unsigned str)] = [] ->
      bytes_at bsegs m (bv_unsigned a2) (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
      ((- (bv_unsigned a2 + zlength str + 1)) mod 8 <= zlength slack) -> (zlength str <= 2^20) ->
      (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + zlength str + 1 + zlength slack + 16 <= 2^47) ->
      stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + FPRINTI_DEPTH <= bv_unsigned sp ->
      (bv_unsigned sp + 64 <= 2^47 - 1) ->
      assp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      (65536 <= fa) -> (fa + zlength fmt <= STATIC_SPLIT) -> (0 < zlength fmt) -> shadow_ok m fa (zlength fmt) ->
      Monad.implM bsegs (outsk OUT_stderr ps (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => fprinti_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFPRINTF_T) fc None m (seg_rom bsegs)).
  Proof.
    intros until canary. intros PCS -> -> SEF FC MR LOW FBY HF P1 PP FPC BY NZ SLK LEN SA1 SA2 ST CEIL LO Q47 SSP MI FRM HFA1 HFA2 FNZ FSO.
    pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE. unfold FPRINTI_DEPTH, VF_DEPTH in LO. unfold STATIC_SPLIT in HFA2.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite length_app in BB. cbn [length] in BB.
    pose proof (bytes_at_bound _ _ _ _ FBY) as FB. unfold zlength in *.
    assert (LZB : length (zbl fmt) = length fmt) by (unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib.zb; apply length_map). rewrite LZB in FB.
    assert (FAR : app_range fa (Z.of_nat (length fmt))) by (left; unfold lowmem_range, KLOWSHADOW_BEG; lia).
    pose proof SSP as [SSP1 SSP2]. unfold AGOT_SSP, ASSP in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (ASTDERR, ASTDERR + 232)]%Z m) as MU. unfold ASTDERR in MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    unfold AFPRINTF_T. ienter.
    (* [comment removed for export] *)
    zs.
    (* [comment removed for export] *)
    assert (SPB' : lo + AFPI_STACK <= bv_unsigned sp) by (unfold AFPI_STACK; lia).
    assert (SA2' : bv_unsigned a2 + Z.of_nat (length str) + 1 + 16 <= 2^47) by lia.
    eapply (fprintf_icpt_prefix_s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo fa (Z_to_bv 64 ASTDERR) MI (fmt_vfi _ FC) LOW ST CEIL
              SPB' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 str slack _ PCS (proj1 (MRT_ssz _ MR)) BY NZ SA1 SA2' LEN).
    unfold fprintf_icpt_K. intros u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6 m1 uu MU2 WM2 MI1 VC1 ST1 FR1.
    assert (MU02 : munch [(lo, bv_unsigned sp)] m m1).
    { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    (* [comment removed for export] *)
    pose proof FR1 as VAC.
    apply (proj1 (rw_cells_app _ _ [_;_;_;_;_;_;_;_] _)) in VAC. destruct VAC as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -112 + Z.of_nat 64)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. clear VAC. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
    ileave.
    unfold A_REAL_VFPRINTF.
    pose proof (@vfprintf_stderr_proof _ St) as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    eapply (implM_post_evt bsegs).
    { (eapply VF with (A := fa) (VA := bv_unsigned sp + -48) (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := [PA_s (map bv_unsigned str)])
                      (lo := lo) (canary := canary); clear VF);
      [ reflexivity
      | reflexivity
      | reflexivity
      | eapply stderr_wfile_stk; [exact SEF| exact MU02| exact WM2| lia]
      | eapply bytes_at_transport; [exact FBY| exact MU02| cbn; lia]
      | exact HF
      | exact P1
      | exact VAA
      | rewrite unsigned_lit by lia; cbn [args_ok arg_ok]; split; [| exact I];
        exists slack; rewrite zb_of_bytes, zlength_map'; unfold zlength;
        split; [eapply bytes_at_transport; [exact BY| exact MU02| cbn; rewrite length_app; cbn [length]; lia]|]; split; [apply bytes_Forall_pos; exact NZ|]; split; [exact SLK|]; split; [lia|];
        split; [lia|]; split; [lia|]; split; [lia|]; split; [unfold VF_FRAME; lia|];
        split; [ eapply (sh_zero_shadow_ok64 _ alloc_ceiling (2^47));
                 [ eapply sh_zero_munch_stack; [exact (proj1 (MRT_ssz _ MR))| exact MU2| try rewrite alloc_ceiling_lit; lia| lia| apply Forall_cons; [cbn [fst]; try rewrite alloc_ceiling_lit; lia| apply Forall_nil]]
                 | (try rewrite alloc_ceiling_lit; lia)| reflexivity| try rewrite alloc_ceiling_lit; lia| try rewrite alloc_ceiling_lit; lia| lia| lia]
               | right; unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END; lia ]
      | exact PP
      | exact FPC
      | rewrite unsigned_lit by lia; exact ST1
      | rewrite unsigned_lit by lia; unfold VF_DEPTH; lia
      | unfold GLOBALS_TOP; lia
      | rewrite unsigned_lit by lia; lia
      | unfold ssp_cells, got_ssp, ssp_guard; split;
          [ eapply (rw_cells_transport bsegs _ m m1); [exact SSP1| exact MU02| exact WM2| cbn; lia]
          | eapply (rw_cells_transport bsegs _ m m1); [exact SSP2| exact MU02| exact WM2| cbn; lia] ]
      | exact MI1
      | exact FRM
      | lia
      | unfold STATIC_SPLIT, zlength; lia
      | rewrite unsigned_lit by lia; lia
      | change (zlength [a2; a3; a4; a5; a6; a7]) with 6; lia
      | eapply MRT_munch; [exact MR| exact MU02| apply Forall_cons; [apply mrt_iv_ok_stack; exact CEIL| apply Forall_nil]]
      | exact CEIL
      | rewrite unsigned_lit by lia; lia
      | unfold zlength; lia
      | unfold zlength; eapply shadow_ok_munch_app; [exact FSO| exact MU02| lia| exact FAR| apply Forall_cons; [apply app_iv_stack; exact CEIL| apply Forall_nil]]
      | unfold zlength; exact FAR ]. }
    cbv beta. intros [] [b3 st3] ms' PO. cbn [snd] in PO.
    unfold vfprintf_stderr_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    unfold AFPRINTF_RET. fix_ret.
    (* [comment removed for export] *)
    eapply (fprintf_icpt_epilogue ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo CEIL SPB');
      [ exact MI3
      | exact ST3
      | eapply (rw_cells_transport bsegs _ m1 m3); [exact FR1| exact MUc| exact WMc| cbn; lia]
      | ].
    intros ST4.
    apply evt_done. subst QQ. cbn [fst snd]. unfold fprinti_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { unfold ASTDERR. apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM2| exact WMc] |]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST4|]. split; [exact SF3|].
    destruct SSP3 as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2. split; [exact G1| exact G2].
  Qed.

  (* [comment removed for export] *)
  Lemma fprinti_u :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      a0 = Z_to_bv 64 ASTDERR -> a1 = Z_to_bv 64 A_FMT_too_big -> bv_unsigned a2 mod 2^32 = 67108864 ->
      stderr_wfile m -> fmt_cells m -> MRT m -> lowsh_at m ->
      stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + FPRINTI_DEPTH <= bv_unsigned sp ->
      (bv_unsigned sp + 64 <= 2^47 - 1) ->
      assp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      Monad.implM bsegs (outsk OUT_stderr pieces_too_big (FLUSH_stderr (St:=St))) ([], st)
        (fun _ bs ms' => fprinti_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFPRINTF_T) fc None m (seg_rom bsegs)).
  Proof.
    intros until canary. intros -> -> HA2 SEF FC MR LOW ST CEIL LO Q47 SSP MI FRM.
    pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE. unfold FPRINTI_DEPTH, VF_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Ra2.
    assert (FBY : bytes_at bsegs m A_FMT_too_big (zbl FMT_too_big)).
    { pose proof (ro_cells_bytes_at bsegs m A_FMT_too_big _ (fmt_tb_bytes m MI)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
    assert (FSO : shadow_ok m A_FMT_too_big 33).
    { apply (lowsh_shadow_ok m A_FMT_too_big 33 LOW); [unfold A_FMT_too_big, AIMG_LO; lia| lia| unfold A_FMT_too_big, AIMG_HI; lia| vm_compute; reflexivity]. }
    assert (FAR : app_range A_FMT_too_big 33) by (left; unfold lowmem_range, A_FMT_too_big, KLOWSHADOW_BEG; lia).
    pose proof SSP as [SSP1 SSP2]. unfold AGOT_SSP, ASSP in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (ASTDERR, ASTDERR + 232)]%Z m) as MU. unfold ASTDERR in MU. pose proof (wmono_refl bsegs m) as WM.
    match goal with |- Monad.implM _ _ _ ?Q _ => set (QQ := Q) end.
    unfold AFPRINTF_T. ienter.
    zs.
    assert (SPB' : lo + AFPI_STACK <= bv_unsigned sp) by (unfold AFPI_STACK; lia).
    unfold A_FMT_too_big.
    eapply (fprintf_icpt_prefix ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo 0x1976e (Z_to_bv 64 ASTDERR) MI (fmt_vfi _ FC) LOW ST CEIL
              SPB' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 _ pcommon_tb_ok).
    unfold fprintf_icpt_K. intros u0 u1 u2 b4 b5 b6 b7 u3 u4 u5 u6 m1 uu MU2 WM2 MI1 VC1 ST1 FR1.
    assert (MU02 : munch [(lo, bv_unsigned sp)] m m1).
    { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    pose proof FR1 as VAC.
    apply (proj1 (rw_cells_app _ _ [_;_;_;_;_;_;_;_] _)) in VAC. destruct VAC as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -112 + Z.of_nat 64)%Z with (bv_unsigned sp + -48)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. clear VAC. cbn [cells_bytes cbytes] in VAA.
    change (le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a2; a3; a4; a5; a6; a7]) in VAA.
    ileave.
    unfold A_REAL_VFPRINTF.
    pose proof (@vfprintf_stderr_proof _ St) as VF. unfold vfprintf_stderr_stmt in VF. cbv zeta in VF.
    eapply (implM_post_evt bsegs).
    { (eapply VF with (A := 0x1976e) (VA := bv_unsigned sp + -48) (fmt := FMT_too_big) (slots := [a2; a3; a4; a5; a6; a7]) (args := [PA_u 67108864])
                      (lo := lo) (canary := canary); clear VF);
      [ reflexivity
      | reflexivity
      | reflexivity
      | eapply stderr_wfile_stk; [exact SEF| exact MU02| exact WM2| lia]
      | eapply bytes_at_transport; [exact FBY| exact MU02| cbn; lia]
      | unfold FMT_too_big; cbn; repeat (apply Forall_cons; [lia|]); apply Forall_nil
      | vm_compute; reflexivity
      | exact VAA
      | rewrite unsigned_lit by lia; cbn [args_ok arg_ok]; split; [| exact I]; split; [lia| exact HA2]
      | exact printf_pieces_too_big
      | reflexivity
      | rewrite unsigned_lit by lia; exact ST1
      | rewrite unsigned_lit by lia; unfold VF_DEPTH; lia
      | unfold GLOBALS_TOP; lia
      | rewrite unsigned_lit by lia; lia
      | unfold ssp_cells, got_ssp, ssp_guard; split;
          [ eapply (rw_cells_transport bsegs _ m m1); [exact SSP1| exact MU02| exact WM2| cbn; lia]
          | eapply (rw_cells_transport bsegs _ m m1); [exact SSP2| exact MU02| exact WM2| cbn; lia] ]
      | exact MI1
      | exact FRM
      | lia
      | change (zlength FMT_too_big) with 33; unfold STATIC_SPLIT; lia
      | rewrite unsigned_lit by lia; lia
      | change (zlength [a2; a3; a4; a5; a6; a7]) with 6; lia
      | eapply MRT_munch; [exact MR| exact MU02| apply Forall_cons; [apply mrt_iv_ok_stack; exact CEIL| apply Forall_nil]]
      | exact CEIL
      | rewrite unsigned_lit by lia; lia
      | change (zlength FMT_too_big) with 33; lia
      | change (zlength FMT_too_big) with 33; eapply shadow_ok_munch_app; [exact FSO| exact MU02| lia| exact FAR| apply Forall_cons; [apply app_iv_stack; exact CEIL| apply Forall_nil]]
      | change (zlength FMT_too_big) with 33; exact FAR ]. }
    cbv beta. intros [] [b3 st3] ms' PO. cbn [snd] in PO.
    unfold vfprintf_stderr_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    unfold AFPRINTF_RET. fix_ret.
    eapply (fprintf_icpt_epilogue ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo CEIL SPB');
      [ exact MI3
      | exact ST3
      | eapply (rw_cells_transport bsegs _ m1 m3); [exact FR1| exact MUc| exact WMc| cbn; lia]
      | ].
    intros ST4.
    apply evt_done. subst QQ. cbn [fst snd]. unfold fprinti_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { unfold ASTDERR. apply (munch_trans _ m m1 m3); [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM2| exact WMc] |]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST4|]. split; [exact SF3|].
    destruct SSP3 as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2. split; [exact G1| exact G2].
  Qed.
End Fprinti.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fmt_stack_split : forall m lo sp, stk bsegs m lo sp -> lo + AFPRINTF_STACK <= sp ->
  stk bsegs m lo (sp - AFPRINTF_STACK) /\ stk bsegs m (sp - AFPRINTF_STACK) sp.
Proof. intros m lo sp ST LO. apply stk_split; [exact ST| unfold AFPRINTF_STACK in *; lia]. Qed.

Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  induction l as [|c l IH]; cbn; intros H; [constructor|].
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [Ha Hb].
  constructor; [apply Z.leb_le in Ha; apply Z.ltb_lt in Hb; lia| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma lrz_of_fprinti : forall (ps : list (list Z)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo0 lo canary m ms mo g K,
  Monad.implM bsegs (outsk OUT_stderr ps (FLUSH_stderr (St:=unit))) ([], tt)
        (fun _ bs ms' => fprinti_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd bs) ms') ms ->
  chan_ok mo 2 -> Forall (fun p => zlength p <= 2^25) ps ->
  lo = bv_unsigned sp - AFPRINTF_STACK -> stk bsegs m lo0 lo -> alloc_ceiling <= lo0 -> lo0 <= lo ->
  K [] ->
  fdiag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo0 canary m mo g K ->
  LRZ ms mo g (t_emit (W 2 (to_bytes (concat ps))) K).
Proof.
  intros until K. intros H CH SM Elo STlo CEIL0 LOLE HK HC. pose proof CEIL0 as CE0. try rewrite alloc_ceiling_lit in CE0.
  assert (H2 : ITree.impl bsegs (at_node bsegs) (stderr_fprintf ps tt)
                 (epost (fun p ms' => fprinti_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (snd p) ms')) ms).
  { unfold stderr_fprintf. apply (stderr_bridge bsegs ps [] tt (fun st' ms' => fprinti_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st' ms')).
    exact H. }
  pose proof (lrzt_stderr_fprintf ps tt mo g CH SM) as RZ. unfold W.
  apply (RZ _ _ K H2 HK). intros [[] []] ms' PO _. cbn [fst snd] in PO. unfold fprinti_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
  subst lo. eapply HC; try eassumption.
  apply (stk_merge _ _ _ (bv_unsigned sp - AFPRINTF_STACK)); [| exact ST'| pose proof (stk_lo_nonneg'' _ _ _ _ ST'); unfold AFPRINTF_STACK in *; lia].
  eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM|].
  pose proof (stk_lo_nonneg'' _ _ _ _ ST') as NN. unfold ASTDERR, AFPRINTF_STACK in *. cbn. lia.
Qed.

Section StrDiag.
  Variables (fa : Z) (FMT : list Z) (pieces : list Z -> list (list Z)) (msg : list byte -> list byte) (np : Z -> Z).
  Hypothesis PCS : pcommon_s_stmt fa.
  Hypothesis FRO : forall m, mem_inv bsegs m -> bytes_at bsegs m fa (zbl FMT).
  Hypothesis FRANGE : Forall (fun c => 0 <= c < 256) FMT.
  Hypothesis P1OK : pass1_ok FMT = true.
  Hypothesis FLEN : 0 < zlength FMT.
  Hypothesis FA1 : 65536 <= fa.
  Hypothesis FA2 : fa + zlength FMT <= STATIC_SPLIT.
  Hypothesis FSO : forall m, lowsh_at m -> shadow_ok m fa (zlength FMT).
  Hypothesis PPs : forall s, zlength s < INT_MAX - 256 -> printf_pieces FMT [PA_s s] = Some (pieces s, np (zlength s)).
  Hypothesis FPCs : forall s, fp_calls (length FMT) FMT [PA_s s] = [].
  Hypothesis MSG : forall s : list byte, to_bytes (concat (pieces (map bv_unsigned s))) = msg s.
  Hypothesis SMALL : forall s, zlength s <= 2^20 -> Forall (fun p => zlength p <= 2^25) (pieces s).

  Lemma so_diag_str_of : so_diag_str_stmt fa msg.
  Proof.
    unfold so_diag_str_stmt. intros until K. intros CH SEF FC MR LOW -> -> BY NZ SLK LEN SA1 SA2 ST CEIL LO Q47 SSP MI FRM HK HC.
    destruct (fmt_stack_split _ _ _ ST LO) as [STlo SThi].
    rewrite <- MSG.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB.
    eapply (lrz_of_fprinti (pieces (map bv_unsigned s))); [| exact CH| apply SMALL; rewrite zlength_map'; exact LEN| reflexivity| exact STlo| exact CEIL| unfold AFPRINTF_STACK in *; lia| exact HK| exact HC].
    eapply (fprinti_s (St:=unit)) with (str := s); try eassumption; try reflexivity.
    - apply FRO. exact MI.
    - apply PPs. rewrite zlength_map'. unfold INT_MAX. lia.
    - apply FPCs.
    - try rewrite alloc_ceiling_lit in CEIL |- *. unfold AFPRINTF_STACK in *. lia.
    - pose proof FPRINTI_DEPTH_le. lia.
    - apply FSO. exact LOW.
  Qed.
End StrDiag.

Theorem so_diag_usage_proof : so_diag_usage_stmt.
Proof.
  apply (so_diag_str_of A_FMT_usage FMT_usage pieces_usage msg_usage (fun l => 14 + l) pcommon_su_ok).
  - intros m MI. pose proof (ro_cells_bytes_at bsegs m A_FMT_usage _ (fmt_usage_bytes m MI)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - apply forall_range_b. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - change (zlength FMT_usage) with 17. lia.
  - unfold A_FMT_usage. lia.
  - change (zlength FMT_usage) with 17. unfold A_FMT_usage, STATIC_SPLIT. lia.
  - intros m L. change (zlength FMT_usage) with 17. apply (lowsh_shadow_ok m A_FMT_usage 17 L); [unfold A_FMT_usage, AIMG_LO; lia| lia| unfold A_FMT_usage, AIMG_HI; lia| vm_compute; reflexivity].
  - intros s Hs. apply printf_pieces_usage. exact Hs.
  - intros s. reflexivity.
  - intros s. unfold pieces_usage, msg_usage. cbn [concat]. rewrite !to_bytes_app, to_bytes_of_bytes, app_nil_r. reflexivity.
  - intros s Hs. unfold pieces_usage. repeat (apply Forall_cons; [unfold zlength in *; cbn; lia |]). apply Forall_nil.
Qed.

Theorem so_diag_cannot_open_proof : so_diag_cannot_open_stmt.
Proof.
  apply (so_diag_str_of A_FMT_cannot_open FMT_cannot_open pieces_cannot_open msg_cannot_open (fun l => 18 + l) pcommon_sco_ok).
  - intros m MI. pose proof (ro_cells_bytes_at bsegs m A_FMT_cannot_open _ (fmt_sco_bytes m MI)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - apply forall_range_b. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - change (zlength FMT_cannot_open) with 21. lia.
  - unfold A_FMT_cannot_open. lia.
  - change (zlength FMT_cannot_open) with 21. unfold A_FMT_cannot_open, STATIC_SPLIT. lia.
  - intros m L. change (zlength FMT_cannot_open) with 21. apply (lowsh_shadow_ok m A_FMT_cannot_open 21 L); [unfold A_FMT_cannot_open, AIMG_LO; lia| lia| unfold A_FMT_cannot_open, AIMG_HI; lia| vm_compute; reflexivity].
  - intros s Hs. apply printf_pieces_cannot_open. exact Hs.
  - intros s. reflexivity.
  - intros s. unfold pieces_cannot_open, msg_cannot_open. cbn [concat]. rewrite !to_bytes_app, to_bytes_of_bytes, app_nil_r. reflexivity.
  - intros s Hs. unfold pieces_cannot_open. repeat (apply Forall_cons; [unfold zlength in *; cbn; lia |]). apply Forall_nil.
Qed.

Theorem so_diag_read_error_proof : so_diag_read_error_stmt.
Proof.
  apply (so_diag_str_of A_FMT_read_error FMT_read_error pieces_read_error msg_read_error (fun l => 20 + l) pcommon_sre_ok).
  - intros m MI. pose proof (ro_cells_bytes_at bsegs m A_FMT_read_error _ (fmt_sre_bytes m MI)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - apply forall_range_b. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - change (zlength FMT_read_error) with 23. lia.
  - unfold A_FMT_read_error. lia.
  - change (zlength FMT_read_error) with 23. unfold A_FMT_read_error, STATIC_SPLIT. lia.
  - intros m L. change (zlength FMT_read_error) with 23. apply (lowsh_shadow_ok m A_FMT_read_error 23 L); [unfold A_FMT_read_error, AIMG_LO; lia| lia| unfold A_FMT_read_error, AIMG_HI; lia| vm_compute; reflexivity].
  - intros s Hs. apply printf_pieces_read_error. exact Hs.
  - intros s. reflexivity.
  - intros s. unfold pieces_read_error, msg_read_error. cbn [concat]. rewrite !to_bytes_app, to_bytes_of_bytes, app_nil_r. reflexivity.
  - intros s Hs. unfold pieces_read_error. repeat (apply Forall_cons; [unfold zlength in *; cbn; lia |]). apply Forall_nil.
Qed.

Lemma msg_refused_eq : to_bytes (concat pieces_too_big) = msg_refused.
Proof. vm_compute. reflexivity. Qed.

Theorem so_diag_refused_proof : so_diag_refused_stmt.
Proof.
  unfold so_diag_refused_stmt. intros until K. intros CH SEF FC MR LOW Ha0 Ha1 Ha2 ST CEIL LO Q47 SSP MI FRM HK HC.
  destruct (fmt_stack_split _ _ _ ST LO) as [STlo SThi].
  rewrite <- msg_refused_eq.
  eapply (lrz_of_fprinti pieces_too_big); [| exact CH| | reflexivity| exact STlo| exact CEIL| unfold AFPRINTF_STACK in *; lia| exact HK| exact HC].
  2:{ unfold pieces_too_big. repeat (apply Forall_cons; [unfold zlength; cbn; lia|]). apply Forall_nil. }
  eapply (fprinti_u (St:=unit)); try eassumption.
  - try rewrite alloc_ceiling_lit in CEIL |- *. unfold AFPRINTF_STACK in *. lia.
  - pose proof FPRINTI_DEPTH_le. lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM bsegs c s Q ms) | _ => idtac end.
Notation mem := (word -> option byte).
End SO_diag.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_icpt_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_icpt_fwrite.
Module SO_diag_fw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.LRzAt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_icpt_fwrite OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_trunA.SO_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_piface.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.      (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).
Local Notation lrzt := (LSO_rz.lrzt bsegs).
Local Notation zbl := OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib.zb.         (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma lrzt_stderr_fwrite : forall {St} (s : list Z) (st : St) mo g,
  chan_ok mo 2 -> 0 < zlength s <= 2^25 ->
  lrzt (stderr_fwrite s st) mo g (map (WriteEv (Z_to_bv 64 2)) (to_bytes s)) (fun r => snd r = st).
Proof.
  intros St s st mo g CH LEN. unfold stderr_fwrite. rewrite (proj2 (Z.ltb_lt 0 (zlength s))) by lia.
  change (to_bytes s) with (to_bytes ([] ++ s)). apply (lrzt_stdio_writev bsegs st mo g 2 [] s CH).
  unfold zlength in *. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fmt_bytes_at : forall m A f, mem_inv bsegs m -> ro_bytes_b bsegs A (zbl f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at bsegs m A (zbl f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at bsegs m A _ (ro_cells_image bsegs m A (zbl f) MI RB H0 ltac:(unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib.zb; rewrite length_map; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma forall_range_b : forall l, forallb (fun c => (0 <=? c) && (c <? 256))%bool l = true -> Forall (fun c => 0 <= c < 256) l.
Proof.
  induction l as [|c l IH]; cbn; intros H; [constructor|].
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [Ha Hb].
  constructor; [apply Z.leb_le in Ha; apply Z.ltb_lt in Hb; lia| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma msg_oom_eq : zbl (concat pieces_oom) = msg_oom.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_eq : zbl (concat pieces_short_hdr) = msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_eq : zbl (concat pieces_cfg_overrun) = msg_overrun.
Proof. vm_compute. reflexivity. Qed.

Section LitDiag.
  Variable A n : Z.
  Variable lit : list Z.          (* [comment removed for export] *)
  Variable msg : list byte.
  Hypothesis msg_eq : zbl lit = msg.
  Hypothesis lit_len : zlength lit = n.
  Hypothesis lit_range : Forall (fun c => 0 <= c < 256) lit.
  Hypothesis n_rng : 0 < n <= 64.
  Hypothesis ro : ro_bytes_b bsegs A (zbl lit) = true.
  Hypothesis A_rng : AIMG_LO <= A /\ A + n <= 0xa1000.       (* [comment removed for export] *)
  Hypothesis glob_ok : glob_ok_b A n = true.                   (* [comment removed for export] *)

  Lemma so_diag_lit_of : so_diag_lit_stmt A n msg.
  Proof.
    unfold so_diag_lit_stmt. intros until K. intros CH SEF IC RC LOW Ha0 Ha1 Ha2 Ha3 ST CEIL LO SSP MI HK HC.
    rewrite <- msg_eq.
    pose proof A_rng as AR. unfold AIMG_LO in AR.
    assert (EA : bv_unsigned a0 = A) by (rewrite Ha0, unsigned_lit; lia).
    assert (SOK : shadow_ok m A n).
    { apply (lowsh_shadow_ok m A n); [exact LOW| unfold AIMG_LO; lia| lia| unfold AIMG_HI; lia| exact glob_ok]. }
    assert (HA : app_range A n) by (left; unfold lowmem_range, KLOWSHADOW_BEG; lia).
    pose proof (@fwrite_icpt_ok _ unit ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc m tt lo canary lit towrite_proof IC RC MI SEF
                  ltac:(rewrite EA; apply fmt_bytes_at; [exact MI | exact ro | lia | lia])
                  lit_range ltac:(lia)
                  ltac:(rewrite lit_len; exact Ha1) Ha2 Ha3 ST CEIL LO
                  ltac:(left; rewrite EA; try rewrite alloc_ceiling_lit in CEIL; lia)
                  ltac:(left; rewrite EA; lia)
                  ltac:(rewrite EA, lit_len; exact HA) ltac:(rewrite EA, lit_len; exact SOK) SSP) as H.
    unfold implM in H.
    pose proof (lrzt_stderr_fwrite lit tt mo g CH ltac:(lia)) as RZ.
    change (zbl lit) with (to_bytes lit). unfold W. unfold AFWRITE_T.
    apply (RZ _ _ K H HK). intros [[] []] ms' PO _. cbn [fst snd] in PO. unfold fwrite_icpt_post in PO.
    destruct PO as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & SF' & SSP' & _).
    eapply HC; eassumption.
  Qed.
End LitDiag.

Theorem so_diag_oom_proof : so_diag_oom_stmt.
Proof.
  apply (so_diag_lit_of A_MSG_oom 19 (concat pieces_oom));
    [apply msg_oom_eq | reflexivity | | lia | vm_compute; reflexivity | unfold A_MSG_oom, AIMG_LO; lia | vm_compute; reflexivity].
  apply forall_range_b. vm_compute. reflexivity.
Qed.
Theorem so_diag_short_proof : so_diag_short_stmt.
Proof.
  apply (so_diag_lit_of A_MSG_short 31 (concat pieces_short_hdr));
    [apply msg_short_eq | reflexivity | | lia | vm_compute; reflexivity | unfold A_MSG_short, AIMG_LO; lia | vm_compute; reflexivity].
  apply forall_range_b. vm_compute. reflexivity.
Qed.
Theorem so_diag_overrun_proof : so_diag_overrun_stmt.
Proof.
  apply (so_diag_lit_of A_MSG_overrun 31 (concat pieces_cfg_overrun));
    [apply msg_overrun_eq | reflexivity | | lia | vm_compute; reflexivity | unfold A_MSG_overrun, AIMG_LO; lia | vm_compute; reflexivity].
  apply forall_range_b. vm_compute. reflexivity.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
End SO_diag_fw.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_vprintf.
Module SO_emit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Image OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fwritex OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface.F_fmt_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_pop_arg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_core OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_printf_snsink OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.F_vsnprintf.F_vfprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_mlib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Printf_pieces.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_str3.ICPT_str OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcleaf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.ICPT_pcdefs2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.ICPT_pcommon_dn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_vfprintf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_vprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSO_rz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_base.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_piface.   (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_fprintf.SO_fwritex_stdout OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.SO_fprintf.SO_vfprintf_stdout SO_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_trunA.SO_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.      (* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.LiaClosure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac arith_goal := lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac
  | |- ~ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- False => idtac | |- True => idtac
  end.   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac lia ::= lia3.
Local Ltac lia ::= lia4.
Local Ltac tlia ::= tlia4.
Local Ltac flia ::= first [ assumption | slim; lia ].   (* [comment removed for export] *)

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM bsegs c s Q ms) | _ => idtac end.

Notation mem := (word -> option byte).
Local Notation LRZ := (LRz.LRZ bsegs).
Local Notation lrzt := (LSO_rz.lrzt bsegs).

(* [comment removed for export] *)
Definition FMT_emitd : list Z := [37; 100; 10; 0].      (* [comment removed for export] *)
Definition A_FMT_emitd : Z := 0x1486b.
Definition EMITD_PIECES : list (list Z) := [[]; []; [48]; []; [10]].

Lemma printf_pieces_emitd : printf_pieces FMT_emitd [PA_i 0] = Some (EMITD_PIECES, 2).
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition EMITD_DEPTH : Z := 80 + 48 + 48 + VF_DEPTH.

Lemma EMITD_DEPTH_le : EMITD_DEPTH <= AEMIT_STACK.
Proof. unfold EMITD_DEPTH, AEMIT_STACK, VF_DEPTH. lia. Qed.

(* [comment removed for export] *)
Lemma fmt_vpi : forall m, fmt_cells m -> vpi_cells m.
Proof. intros m (IC & CF & _ & _ & _ & _ & _ & RV & _). exact (conj IC (conj CF RV)). Qed.
Lemma fmt_vfi : forall m, fmt_cells m -> vfi_cells m.
Proof. intros m (IC & CF & _ & _ & RVF & _). exact (conj IC (conj CF RVF)). Qed.

Lemma fmt_cells_munch_stack : forall u v m m', fmt_cells m -> munch [(u, v)] m m' -> alloc_ceiling <= u -> fmt_cells m'.
Proof.
  intros u v m m' H MU Hu. try rewrite alloc_ceiling_lit in Hu.
  destruct H as (IC & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  split; [eapply icpt_cells_munch; [exact IC| exact MU| unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil]|].
  repeat match goal with |- _ /\ _ => split end;
    (eapply ro_cells_transport; [eassumption| exact MU| cbn; lia]).
Qed.

(* [comment removed for export] *)
Lemma fmt_emitd_bytes : forall m, mem_inv bsegs m -> bytes_at bsegs m A_FMT_emitd (zb FMT_emitd).
Proof.
  intros m MI.
  pose proof (ro_cells_bytes_at bsegs m A_FMT_emitd _ (ro_cells_image bsegs m A_FMT_emitd (zb FMT_emitd) MI ltac:(vm_compute; reflexivity) ltac:(unfold A_FMT_emitd; lia) ltac:(cbn; unfold A_FMT_emitd; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

(* [comment removed for export] *)
Lemma fmt_emitd_shadow : forall m, lowsh_at m -> shadow_ok m A_FMT_emitd 4.
Proof. intros m L. apply (lowsh_shadow_ok m A_FMT_emitd 4 L); [unfold A_FMT_emitd, AIMG_LO; lia| lia| unfold A_FMT_emitd, AIMG_HI; lia| vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Section Shell.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  Definition emitd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
      (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp); (ASTDOUT, ASTDOUT + 232); (ASTDOUT_BUF, ASTDOUT_BUF + 1024)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ frm0 fc'
      /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ stdout_file m' (get_so st')
      /\ assp_cells m' canary.

  Lemma emitd_gen :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St) (lo : Z) (canary : word),
      fwritex_stdout_stmt ->
      stdout_file m (get_so st) ->
      fmt_cells m -> MRT m -> lowsh_at m ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + EMITD_DEPTH <= bv_unsigned sp ->
      (bv_unsigned sp + 64 <= 2^47 - 1) ->
      assp_cells m canary -> mem_inv bsegs m -> frm0 fc ->
      Monad.implM bsegs (stdout_towrite get_so set_so ;;; outsk (stdout_fwritex get_so set_so) EMITD_PIECES (mret tt)) st
            (emitd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 AEMIT) fc None m (seg_rom bsegs)).
  Proof using GS SS.
    intros until canary. intros FWX SF FC MR LOW HA1 ST CEIL LO Q47 SSP MI FRM.
    pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE. unfold EMITD_DEPTH, VF_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
    pose proof SSP as [SSP1 SSP2]. unfold AGOT_SSP, ASSP in SSP1, SSP2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (ASTDOUT, ASTDOUT + 232); (ASTDOUT_BUF, ASTDOUT_BUF + 1024)]%Z m) as MU.
    unfold ASTDOUT, ASTDOUT_BUF in MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.
    unfold AEMIT. ienter.
    carve_frame 80%nat ST.
    do 15 zs.
    (* [comment removed for export] *)
    zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (vprintf_icpt_prefix (Z_to_bv 64 0x82378) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mm lo 0x1486b
                (Z_to_bv 64 (bv_unsigned sp + -56)));
      [ exact MI
      | apply fmt_vpi; eapply fmt_cells_munch_stack; [exact FC| exact MU1| exact CEIL]
      | eapply lowsh_at_munch_stack; [exact LOW| exact MU1| exact WM| exact CEIL]
      | rewrite unsigned_lit by lia; exact ST
      | exact CEIL
      | rewrite unsigned_lit by lia; unfold AVPI_STACK; lia
      | exact pcommon_dn_ok
      | ] end.
    intros u0 u1 u2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 uu MU2 WM2 MI1 VC1 ST1 FR1.
    rewrite unsigned_lit in MU2, ST1, FR1 |- * by lia.
    (* [comment removed for export] *)
    unfold A_REAL_VPRINTF. do 8 zs.
    (* [comment removed for export] *)
    eapply (vfprintf_icpt_prefix (Z_to_bv 64 AVPRINTF_RET) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp
              (Z_to_bv 64 84075) (Z_to_bv 64 (bv_unsigned sp + -56)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 lo 0x1486b
              (Z_to_bv 64 0xa5e18) (Z_to_bv 64 (bv_unsigned sp + -56)));
      [ exact MI1
      | apply fmt_vfi; eapply fmt_cells_munch_stack; [| exact MU2| lia]; eapply fmt_cells_munch_stack; [exact FC| exact MU1| exact CEIL]
      | eapply lowsh_at_munch_stack; [| exact MU2| exact WM2| lia]; eapply lowsh_at_munch_stack; [exact LOW| exact MU1| exact WM| exact CEIL]
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp + -128) with (bv_unsigned sp + -80 + -48) by lia; exact ST1
      | exact CEIL
      | rewrite unsigned_lit by lia; unfold AVFI_STACK; lia
      | exact pcommon_dn_ok
      | ].
    intros v0 v1 v2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m2 MU3 WM3 MI2 VC2 ST2 FR2.
    rewrite unsigned_lit in MU3, ST2, FR2 |- * by lia.
    (* [comment removed for export] *)
    assert (MU0_2 : munch [(lo, bv_unsigned sp + -80)] m0 m2).
    { apply (munch_trans _ m0 m1 m2); [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM0_2 : wmono bsegs m0 m2) by (eapply wmono_trans; [exact WM2| exact WM3]).
    assert (MU02 : munch [(lo, bv_unsigned sp)] m m2).
    { apply (munch_trans _ m m0 m2); [exact MU1|]. eapply munch_weaken; [| exact MU0_2]. unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM02 : wmono bsegs m m2) by (eapply wmono_trans; [exact WM| exact WM0_2]).
    (* [comment removed for export] *)
    pose proof FR as FR0.
    apply (proj1 (rw_cells_app _ _ [_;_;_] _)) in FR0. destruct FR0 as [_ VAC]. cbn [cells_size csize Nat.add app] in VAC.
    replace (bv_unsigned sp + -80 + Z.of_nat 24)%Z with (bv_unsigned sp + -56)%Z in VAC by lia.
    pose proof (rw_cells_bytes_at' _ _ _ _ VAC) as VAA. clear VAC. cbn [cells_bytes cbytes] in VAA.
    change (le8 a1 ++ le8 a2 ++ le8 a3 ++ le8 a4 ++ le8 a5 ++ le8 a6 ++ le8 a7 ++ []) with (u64s [a1; a2; a3; a4; a5; a6; a7]) in VAA.
    assert (VAA2 : va_area m2 (bv_unsigned sp + -56) [a1; a2; a3; a4; a5; a6; a7]).
    { unfold va_area. eapply (bytes_at_transport bsegs [(lo, bv_unsigned sp + -80)]); [exact VAA| exact MU0_2| cbn; lia]. }
    clear VAA.
    ileave.
    unfold A_REAL_VFPRINTF.
    pose proof (vfprintf_stdout_proof get_so set_so GS SS FWX) as VF. unfold vfprintf_stdout_stmt in VF. cbv zeta in VF.
    eapply (implM_post_evt bsegs).
    { (eapply VF with (A := A_FMT_emitd) (VA := bv_unsigned sp + -56) (fmt := FMT_emitd) (slots := [a1; a2; a3; a4; a5; a6; a7]) (args := [PA_i 0])
                     (r := 2) (lo := lo) (canary := canary); clear VF);
      [ reflexivity
      | reflexivity
      | reflexivity
      | eapply stdout_file_stk; [exact SF| exact MU02| exact WM02| lia]
      | apply fmt_emitd_bytes; exact MI2
      | unfold FMT_emitd; repeat (apply Forall_cons; [lia|]); apply Forall_nil
      | vm_compute; reflexivity
      | exact VAA2
      | rewrite unsigned_lit by lia; cbn [args_ok arg_ok]; split; [|exact I]; split; [lia|]; rewrite HA1; reflexivity
      | exact printf_pieces_emitd
      | vm_compute; reflexivity
      | rewrite unsigned_lit by lia; exact ST2
      | rewrite unsigned_lit by lia; unfold VF_DEPTH; lia
      | unfold GLOBALS_TOP; lia
      | rewrite unsigned_lit by lia; lia
      | unfold ssp_cells, got_ssp, ssp_guard; split;
          [ eapply (rw_cells_transport bsegs _ m0 m2); [exact SSP1| exact MU0_2| exact WM0_2| cbn; lia]
          | eapply (rw_cells_transport bsegs _ m0 m2); [exact SSP2| exact MU0_2| exact WM0_2| cbn; lia] ]
      | exact MI2
      | exact FRM
      | unfold A_FMT_emitd; lia
      | change (zlength FMT_emitd) with 4; unfold A_FMT_emitd, STATIC_SPLIT; lia
      | rewrite unsigned_lit by lia; lia
      | change (zlength [a1; a2; a3; a4; a5; a6; a7]) with 7; lia
      | eapply MRT_munch; [exact MR| exact MU02| apply Forall_cons; [apply mrt_iv_ok_stack; exact CEIL| apply Forall_nil]]
      | exact CEIL
      | rewrite unsigned_lit by lia; lia
      | change (zlength FMT_emitd) with 4; lia
      | change (zlength FMT_emitd) with 4; apply fmt_emitd_shadow; eapply lowsh_at_munch_stack; [exact LOW| exact MU02| exact WM02| exact CEIL]
      | change (zlength FMT_emitd) with 4; left; unfold lowmem_range, A_FMT_emitd, KLOWSHADOW_BEG; lia ]. }
    cbv beta. intros [] st' ms' PO.
    unfold vfprintf_stdout_post in PO. rewrite !unsigned_lit in PO by lia.
    destruct PO as (y5 & y6 & y7 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y28 & y29 & y30 & y31 & Ft & fc' & m3 & -> & MUc & WMc & MI3 & FRM' & FOK & ST3 & SF3 & SSP3).
    unfold AVFPRINTF_RET. fix_ret.
    (* [comment removed for export] *)
    assert (Esp2 : exists sp2 : word, sp2 = Z_to_bv 64 (bv_unsigned sp + -128)) by (eexists; reflexivity).
    destruct Esp2 as [sp2 Esp2].
    assert (Hsp2 : bv_unsigned sp2 = bv_unsigned sp + -128) by (rewrite Esp2; apply unsigned_lit; lia).
    rewrite <- Hsp2.
    eapply (vfprintf_icpt_epilogue (Z_to_bv 64 AVPRINTF_RET) sp2 gp tp
              (Z_to_bv 64 84075) (Z_to_bv 64 (bv_unsigned sp + -56)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo CEIL);
      [ rewrite Hsp2; unfold AVFI_STACK; lia
      | exact MI3
      | rewrite Hsp2; exact ST3
      | rewrite Hsp2; eapply (rw_cells_transport bsegs _ m2 m3); [exact FR2| exact MUc| exact WMc| cbn; lia]
      | ].
    intros ST4. rewrite Hsp2 in ST4. subst sp2. clear Hsp2.
    unfold AVPRINTF_RET. fix_ret.
    (* [comment removed for export] *)
    assert (MU1_3 : munch [(lo, bv_unsigned sp + -128); (679448, 679448 + 232); (6279296, 6279296 + 1024)] m1 m3).
    { apply (munch_trans _ m1 m2 m3); [eapply munch_weaken; [| exact MU3] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM1_3 : wmono bsegs m1 m3) by (eapply wmono_trans; [exact WM3| exact WMc]).
    assert (Esp1 : exists sp1 : word, sp1 = Z_to_bv 64 (bv_unsigned sp + -80)) by (eexists; reflexivity).
    destruct Esp1 as [sp1 Esp1].
    assert (Hsp1 : bv_unsigned sp1 = bv_unsigned sp + -80) by (rewrite Esp1; apply unsigned_lit; lia).
    replace (bv_unsigned sp + -128) with (bv_unsigned sp1 + -48) by lia.
    eapply (vprintf_icpt_epilogue (Z_to_bv 64 0x82378) sp1 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo CEIL);
      [ rewrite Hsp1; unfold AVPI_STACK; lia
      | exact MI3
      | rewrite Hsp1; replace (bv_unsigned sp + -80 + -48) with (bv_unsigned sp + -128) by lia; exact ST4
      | rewrite Hsp1; eapply (rw_cells_transport bsegs _ m1 m3); [exact FR1| exact MU1_3| exact WM1_3| cbn; lia]
      | ].
    intros ST5. rewrite Hsp1 in ST5. subst sp1. clear Hsp1.
    fix_ret.
    (* [comment removed for export] *)
    assert (MU0_3 : munch [(lo, bv_unsigned sp + -80); (679448, 679448 + 232); (6279296, 6279296 + 1024)] m0 m3).
    { apply (munch_trans _ m0 m2 m3); [eapply munch_weaken; [| exact MU0_2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; intros; lia. }
    assert (WM0_3 : wmono bsegs m0 m3) by (eapply wmono_trans; [exact WM0_2| exact WMc]).
    pose proof (rw_cells_transport bsegs _ m0 m3 _ _ FR MU0_3 WM0_3 ltac:(cbn; lia)) as FR3.
    clear FR FR1 FR2 ST ST1 ST2 ST3 ST4 MI MI1 MI2 VC1 VC2 VAA2.
    zs. zs. zs.
    release_frame FR3 ST5 (bv_unsigned sp).
    apply evt_done. unfold emitd_post. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split. { unfold ASTDOUT, ASTDOUT_BUF. apply (munch_trans _ m m0 m3); [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU0_3]]; unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM| exact WM0_3] |]. split; [exact MI3|]. split; [exact FRM'|]. split; [exact FOK|].
    split; [exact ST5|]. split; [exact SF3|].
    destruct SSP3 as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2. split; [exact G1| exact G2].
  Qed.
End Shell.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StdoutModel.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.
  Local Notation OUT := (stdout_fwritex get_so set_so).

  Lemma zlength_app' : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
  Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

  Lemma lrzt_stdout_towrite : forall st mo g (R : unit * stdout_st -> Prop),
    R (tt, if so_active st then st else mkStdout true [] (so_lbf_nl st) (so_first st)) ->
    lrzt (stdout_towrite get_so set_so st) mo g [] R.
  Proof. intros st mo g R HR. unfold stdout_towrite. apply lrzt_upd_so. exact HR. Qed.

  (* [comment removed for export] *)
  Lemma lrzt_fwritex_keep : forall s buf lbf first mo g,
    zlength buf + zlength s <= STDOUT_BUFSIZ -> (lbf = false \/ after_last_nl s = 0) ->
    lrzt (OUT s (mkStdout true buf lbf first)) mo g [] (fun r => snd r = mkStdout true (buf ++ s) lbf first).
  Proof.
    intros s buf lbf first mo g B NL. unfold stdout_fwritex.
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (tt, mkStdout true buf lbf first))); [apply lrzt_stdout_towrite; reflexivity|].
    intros [] s1 E. injection E as ->.
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (mkStdout true buf lbf first, mkStdout true buf lbf first))); [apply lrzt_rd_so; reflexivity|].
    intros so s1 E. injection E as -> ->. cbn [so_buf so_lbf_nl so_active so_first].
    destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength s)) as [X|X]; [lia|].
    destruct lbf.
    - destruct NL as [NL|NL]; [discriminate|]. rewrite NL. cbn [Z.ltb Z.to_nat skipn].
      eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (tt, mkStdout true buf true first))); [apply lrzt_mret; reflexivity|].
      intros [] s1 E. injection E as ->. apply lrzt_upd_so. reflexivity.
    - apply lrzt_upd_so. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma lrzt_fwritex_flushline : forall s buf first mo g,
    chan_ok mo 1 -> zlength buf + zlength s <= STDOUT_BUFSIZ -> after_last_nl s = zlength s -> 0 < zlength s ->
    lrzt (OUT s (mkStdout true buf true first)) mo g (map (WriteEv (Z_to_bv 64 1)) (to_bytes (buf ++ s)))
        (fun r => snd r = mkStdout true [] (if first then false else true) false).
  Proof.
    intros s buf first mo g CH B NL POS. unfold stdout_fwritex.
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (tt, mkStdout true buf true first))); [apply lrzt_stdout_towrite; reflexivity|].
    intros [] s1 E. injection E as ->.
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => r = (mkStdout true buf true first, mkStdout true buf true first))); [apply lrzt_rd_so; reflexivity|].
    intros so s1 E. injection E as -> ->. cbn [so_buf so_lbf_nl so_active so_first].
    destruct (Z.ltb_spec (STDOUT_BUFSIZ - zlength buf) (zlength s)) as [X|X]; [lia|].
    rewrite NL. rewrite (proj2 (Z.ltb_lt 0 (zlength s))) by exact POS.
    rewrite firstn_all2 by (unfold zlength; lia). rewrite skipn_all2 by (unfold zlength; lia).
    eapply lrzt_mbind_nil_r.
    - eapply lrzt_mono; [apply lrzt_stdout_writefn; [exact CH| cbn [so_buf]; unfold STDOUT_BUFSIZ in B; lia]|]. intros r Hr; exact Hr.
    - intros [] s1 E. cbn [snd so_first] in E. subst s1. apply lrzt_upd_so. cbn [snd so_active so_buf so_lbf_nl so_first]. reflexivity.
  Qed.

  Local Notation EMRUN := (stdout_towrite get_so set_so ;;; outsk OUT EMITD_PIECES (mret tt)).

  Ltac em_keep B :=
    eapply (lrzt_mbind_nil_l bsegs _ _ _ _ _ _ (fun r => snd r = B)); [ | intros [] ? E; cbn [snd] in E; subst ].

  (* [comment removed for export] *)
  Lemma lrzt_emit_first : forall mo g, chan_ok mo 1 ->
    lrzt (EMRUN stdout_init) mo g (W 1 emit_line) (fun r => snd r = emit_after_first).
  Proof.
    intros mo g CH. unfold stdout_init, emit_after_first, W, emit_line. cbn [outsk].
    em_keep (mkStdout true [] true true); [apply lrzt_stdout_towrite; reflexivity|].
    em_keep (mkStdout true ([] ++ []) true true); [apply lrzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([] ++ []) true true); [apply lrzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([] ++ [48]) true true); [apply lrzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    em_keep (mkStdout true ([48] ++ []) true true); [apply lrzt_fwritex_keep; [apply Z.leb_le; reflexivity| right; reflexivity]|]. cbn [app].
    eapply lrzt_mbind_nil_r.
    - change [Z_to_bv 8 48; Z_to_bv 8 10] with (to_bytes ([48] ++ [10])).
      apply (lrzt_fwritex_flushline [10] [48] true mo g CH); [apply Z.leb_le; reflexivity| reflexivity| reflexivity].
    - intros [] s1 E. cbn [snd] in E. subst s1. apply lrzt_mret. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma lrzt_emit_again : forall mo g buf, chan_ok mo 1 -> zlength buf + 2 <= STDOUT_BUFSIZ ->
    lrzt (EMRUN (mkStdout true buf false false)) mo g (W 1 []) (fun r => snd r = mkStdout true (buf ++ [48; 10]) false false).
  Proof.
    intros mo g buf CH B. unfold W. cbn [outsk map].
    em_keep (mkStdout true buf false false); [apply lrzt_stdout_towrite; reflexivity|].
    em_keep (mkStdout true (buf ++ []) false false); [apply lrzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true (buf ++ []) false false); [apply lrzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true (buf ++ [48]) false false); [apply lrzt_fwritex_keep; [unfold zlength in *; cbn [length]; lia| left; reflexivity]|].
    em_keep (mkStdout true ((buf ++ [48]) ++ []) false false); [apply lrzt_fwritex_keep; [rewrite zlength_app'; unfold zlength in *; cbn [length]; lia| left; reflexivity]|]. rewrite app_nil_r.
    em_keep (mkStdout true ((buf ++ [48]) ++ [10]) false false); [apply lrzt_fwritex_keep; [rewrite zlength_app'; unfold zlength in *; cbn [length]; lia| left; reflexivity]|].
    apply lrzt_mret. cbn [snd]. rewrite <- app_assoc. reflexivity.
  Qed.
End StdoutModel.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma emit_stack_split : forall m lo sp, stk bsegs m lo sp -> lo + AEMIT_STACK <= sp ->
  stk bsegs m lo (sp - AEMIT_STACK) /\ stk bsegs m (sp - AEMIT_STACK) sp.
Proof. intros m lo sp ST LO. apply stk_split; [exact ST| unfold AEMIT_STACK in *; lia]. Qed.

Theorem so_emit_first_proof : so_emit_first_stmt.
Proof.
  unfold so_emit_first_stmt. intros until K. intros CH SF FC MR LOW HA1 ST CEIL LO Q47 SSP MI FRM HK HC.
  destruct (emit_stack_split _ _ _ ST LO) as [STlo SThi].
  pose proof (emitd_gen (fun s : stdout_st => s) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m stdout_init (bv_unsigned sp - AEMIT_STACK) canary fwritex_stdout_proof SF FC MR LOW HA1 SThi
                ltac:(unfold AEMIT_STACK in *; lia) ltac:(pose proof EMITD_DEPTH_le; lia) Q47 SSP MI FRM) as H.
  unfold Monad.implM in H.
  pose proof (lrzt_emit_first mo g CH) as RZ.
  apply (RZ _ _ K H HK). intros [[] st'] ms' PO E. cbn [snd] in E. subst st'. cbn [fst snd] in PO. unfold emitd_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
  eapply HC; try eassumption.
  apply (stk_merge _ _ _ (bv_unsigned sp - AEMIT_STACK)); [| exact ST'| unfold AEMIT_STACK in *; lia].
  eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM|].
  pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE. unfold ASTDOUT, ASTDOUT_BUF, AEMIT_STACK in *. cbn. lia.
Qed.

Theorem so_emit_again_proof : so_emit_again_stmt.
Proof.
  unfold so_emit_again_stmt. intros until K. intros CH SF B HF FC MR LOW HA1 ST CEIL LO Q47 SSP MI FRM HK HC.
  destruct (emit_stack_split _ _ _ ST LO) as [STlo SThi].
  pose proof (emitd_gen (fun s : stdout_st => s) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (mkStdout true buf false false) (bv_unsigned sp - AEMIT_STACK) canary fwritex_stdout_proof SF FC MR LOW HA1 SThi
                ltac:(unfold AEMIT_STACK in *; lia) ltac:(pose proof EMITD_DEPTH_le; lia) Q47 SSP MI FRM) as H.
  unfold Monad.implM in H.
  pose proof (lrzt_emit_again mo g buf CH B) as RZ.
  apply (RZ _ _ K H HK). intros [[] st'] ms' PO E. cbn [snd] in E. subst st'. cbn [fst snd] in PO. unfold emitd_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP').
  eapply HC; try eassumption.
  apply (stk_merge _ _ _ (bv_unsigned sp - AEMIT_STACK)); [| exact ST'| unfold AEMIT_STACK in *; lia].
  eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM|].
  pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE. unfold ASTDOUT, ASTDOUT_BUF, AEMIT_STACK in *. cbn. lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM bsegs c s Q ms) | _ => idtac end.
Notation mem := (word -> option byte).
End SO_emit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface CJ_tree AShadow CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import Exit SO_base Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_trunA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_trunA.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import Drv_base Drv_iface2 Drv_traces CJ_fuzz_iface Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require DrvTop.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.DrvTop.Drv_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import DrvTop.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.

Theorem a_main_closed04 : forall (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface) (S_LIB : list (list Z)),
  TINV TI 0 [] -> drv_traces_ok TI -> (forall tr, In tr S_LIB -> STAT TI tr) -> 4 * FUZZ_NP (2^26) <= NPMAX TI ->
  llvmfuzz_stmt AI TI S_LIB ->
  a_main_stmt04 AI DI.
Proof.
  intros AI DI TI S_LIB TI0 TROK LIBOK NPOK FUZZ.
  apply (a_main_proof04 AI DI TI S_LIB TI0 TROK LIBOK NPOK FUZZ).
  - exact SO_exit.so_exit_proof.
  - exact SO_diag.so_diag_refused_proof.
  - exact SO_diag.so_diag_read_error_proof.
  - exact SO_diag.so_diag_cannot_open_proof.
  - exact SO_diag_fw.so_diag_short_proof.
  - exact SO_diag_fw.so_diag_overrun_proof.
  - exact SO_emit.so_emit_first_proof.
  - exact SO_emit.so_emit_again_proof.
  - exact SO_diag.so_diag_usage_proof.
Qed.
End CeilWrap.
