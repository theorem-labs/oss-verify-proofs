(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from P/SO_emit.v (module SO_exit): the stdout flush over rzt, rz_at_exit and so_exit_proof restated over BudgetWit.Rzb.rzb, with their released proofs. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: chan_ok also gives the channel reader, so its halves go to rzt_stdio_writev_b and rzt_ioctl_b, as P/SO_emit.v does there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_emit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RegsEquiv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NodesSound OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.Startup_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_fmt_fp_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.PImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_model OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_rz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_emit.SO_stdio_exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_emit.SO_exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb Lib_RzNodesImplB P_SO_rzB P_SO_fprintfB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation rztb := (rzt_b psegs).

Section StdoutModel.
  Let get_so : stdout_st -> stdout_st := fun s => s.
  Let set_so : stdout_st -> stdout_st -> stdout_st := fun so _ => so.

  Lemma rzt_rd_so_b : forall st mo (R : stdout_st * stdout_st -> Prop), R (st, st) -> rztb (rd_so get_so st) mo [] R.
  Proof.
    intros st mo R HR. unfold rd_so. eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_mget_b; reflexivity|].
    intros a s' E. injection E as -> ->. apply rzt_mret_b. exact HR.
  Qed.

  Lemma rzt_upd_so_b : forall f st mo (R : unit * stdout_st -> Prop), R (tt, f st) -> rztb (upd_so get_so set_so f st) mo [] R.
  Proof. intros f st mo R HR. unfold upd_so. apply rzt_mupd_b. exact HR. Qed.

  Lemma rzt_stdout_stdio_write_b : forall s st mo,
    chan_ok mo 1 -> zlength (so_buf st) + zlength s <= 67108864 ->
    rztb (stdout_stdio_write get_so set_so s st) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st ++ s)))
        (fun r => snd r = mkStdout true [] (so_lbf_nl st) (so_first st)).
  Proof.
    intros s st mo CH B. unfold stdout_stdio_write.
    eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_rd_so_b; reflexivity|]. intros so s' E. injection E as -> ->.
    eapply rzt_mbind_nil_r_b; [apply (rzt_stdio_writev_b psegs st mo 1 (so_buf st) s (proj1 CH) (proj2 CH)); exact B|].
    intros [] s' E. cbn [snd] in E. subst s'. apply rzt_upd_so_b. reflexivity.
  Qed.

  Lemma rzt_stdout_writefn_b : forall s st mo,
    chan_ok mo 1 -> zlength (so_buf st) + zlength s <= 67108864 ->
    rztb (stdout_writefn get_so set_so s st) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st ++ s)))
        (fun r => snd r = mkStdout true [] (if so_first st then false else so_lbf_nl st) false).
  Proof.
    intros s st mo CH B. unfold stdout_writefn.
    eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_rd_so_b; reflexivity|]. intros so s' E. injection E as -> ->.
    destruct st as [act buf lbf first]. cbn [so_first so_buf so_lbf_nl] in *. destruct first.
    - eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => snd r = mkStdout act buf false false)).
      + eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => r = (tt, mkStdout act buf lbf false))); [apply rzt_upd_so_b; reflexivity|].
        intros [] s1 E. injection E as ->.
        eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => (exists err, fst r = SErr err) /\ snd r = mkStdout act buf lbf false));
          [eapply (rzt_ioctl_b psegs); [exact (proj1 CH)| discriminate|]; intros err; split; [exists err; reflexivity| reflexivity] |].
        intros r s1 [[err E1] E2]. cbn [fst snd] in E1, E2. subst r s1. apply rzt_upd_so_b. reflexivity.
      + intros [] s1 E. cbn [snd] in E. subst s1.
        eapply rzt_mono_b; [apply rzt_stdout_stdio_write_b; [exact CH| cbn [so_buf]; exact B]|]. intros [[] s2] E2. exact E2.
    - eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => r = (tt, mkStdout act buf lbf false))); [apply rzt_mret_b; reflexivity|].
      intros [] s1 E. injection E as ->.
      eapply rzt_mono_b; [apply rzt_stdout_stdio_write_b; [exact CH| cbn [so_buf]; exact B]|]. intros [[] s2] E2. exact E2.
  Qed.

  Lemma rzt_stdout_exit_flush_b : forall st mo,
    chan_ok mo 1 -> zlength (so_buf st) <= 67108864 ->
    rztb (stdout_exit_flush get_so set_so st) mo (map (WriteEv (Z_to_bv 64 1)) (to_bytes (so_buf st))) (fun _ => True).
  Proof.
    intros st mo CH B. unfold stdout_exit_flush.
    eapply (rzt_mbind_nil_l_b psegs _ _ _ _ _ (fun r => r = (st, st))); [apply rzt_rd_so_b; reflexivity|]. intros so s' E. injection E as -> ->.
    destruct (Z.ltb_spec 0 (zlength (so_buf st))) as [P|N].
    - rewrite <- (app_nil_r (so_buf st)) at 1. eapply rzt_mono_b; [apply rzt_stdout_writefn_b; [exact CH| unfold zlength in *; cbn [length]; lia]|]. intros; exact I.
    - replace (so_buf st) with (@nil Z) by (symmetry; apply length_zero_iff_nil; unfold zlength in N; lia). cbn [to_bytes map]. apply rzt_mret_b. exact I.
  Qed.
End StdoutModel.

Lemma rzb_at_exit : forall ms mo code,
  at_node psegs (NExit code) ms -> MOK mo -> 0 <= code < 256 ->
  rzb psegs (mkCfg ms mo) (t_exit (Z_to_bv 64 code) (m_fs mo)).
Proof.
  intros ms mo code Hat [Hh _] Hc. cbn [at_node] in Hat. destruct Hat as [Hsvc H10].
  rewrite <- (bv_and_255_small code Hc), <- H10. change (areg ms 10) with (ms_gpr ms 0).
  destruct Hsvc as [Hs|Hs]; (eapply rzb_exit; [exact Hh | exact Hs | ]); [apply is_exit_no_93 | apply is_exit_no_94].
Qed.

Theorem so_exit_proof_b : so_exit_stmt_b.
Proof.
  unfold so_exit_stmt_b. intros until ph.
  intros HM CH ST TDa EXL GF FA FIN GCX DSO INCB ATX LCH OFL SIN SOU SEU SOF BND SEF GG GU MI Htp Ha0 Hc Ht LO GLO.
  unfold EXIT_DEPTH, GLOBALS_TOP in *.
  pose proof (exit_spec_so so (fun _ _ _ => False) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo code t td0 td1 td2 td3 guard cdt thr sec tm1 ph
                ST TDa EXL GF FA FIN GCX DSO INCB ATX LCH OFL SIN SOU SEU SOF SEF GG GU MI Htp Ha0 Ht LO GLO) as H.
  unfold Driver.exit_model, implM, mbind in H. cbn [io_exit io_S] in H. apply impl_bind_inv in H.
  pose proof (rzt_stdout_exit_flush_b so mo CH ltac:(lia)) as RZ.
  unfold W. unfold t_exit.
  refine (RZ (fun a ms' => ITree.impl psegs (at_node psegs) (msys (NExit code) dec_exit (snd a)) (epost (fun (_ : Empty_set * stdout_st) (_ : machine_state) => False)) ms') _ _ HM _ (t_emit_has_nil _ _) _).
  - eapply impl_mono; [exact H|]. intros [|a] ms'; cbn [epost]; [intros _; exact I| intros X; exact X].
  - intros a ms' Hi _. unfold msys in Hi. fold (t_exit (Z_to_bv 64 code) (m_fs mo)).
    eapply (rzb_impl_enode psegs); [exact HM | exact Hi |]. intros ms1 Hat _. apply rzb_at_exit; [exact Hat | exact HM | exact Hc].
Qed.
