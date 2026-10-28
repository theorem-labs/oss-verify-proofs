(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qx X0qw X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1np X1h7 X1kc X1ka X1kd X1k9 X1l0 X1l1 X1l4 X1l5 X1l6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1oc X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.

Section Main.
Context {RCEIL : RunCeiling}.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FKP : rfree_keeps_ptr_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.
Hypothesis TRUN : rtarget_run_stmt.
Hypothesis RHI : rheap_init_stmt.

#[using="RHF RND RBD RBR MALLOC FREE FKP FPR FWX SWF FWR TOW TRUN"] Lemma main_from_P1 : forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (F : bvmap 5 word) (arg0 arg1 : list byte) (TID : Z) ms,
valid_sp sp0 -> alloc_ceiling = LO sp0 -> valid_argv argv -> valid_envp envp -> argv = [arg0; arg1] -> 0 < TID < 4194304 -> is_mkF F ->
P1 sp0 argv envp uid hw rnd TID F ms ->
implM rsegs (ra <- read_all io_diag raw_malloc raw_free RSTAGE_ubsan (map bv_unsigned arg1) ;;
match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end)
(ps_init alloc_ceiling (reservedZ rsegs)) RQEXIT ms.
Proof.
intros sp0 argv envp uid hw rnd F arg0 arg1 TID ms VSP HCEIL VARGV VENVP EARGV HT MKF HP1.
first [ sf_destruct 31%nat HP1 as t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 fc mm pad -> FR BA HP CJ ERR FRM [stg SG] | sf_fb; destruct HP1 as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & fc & mm & pad & -> & FR & BA & HP & CJ & ERR & FRM & [stg SG]) ].
eapply implM_bind.
{ eapply (main_read_all sp0 argv envp uid hw rnd arg0 arg1 TID s4 s5 s6 s7 s8 s9 s10 s11);
first [exact VSP| exact HCEIL| exact VARGV| exact VENVP| exact EARGV| exact HT| exact RHF| exact RND| exact RBD| exact RBR| exact MALLOC| exact FREE| exact FKP
| exact FPR| exact FWX| exact SWF| exact FWR| exact TOW| exists pad; exact FR| exact BA| exact HP| exact CJ| exact ERR| exact FRM| exact MKF| exact SG]. }
cbv beta. intros ra s' ms' PB. destruct ra as [|buf content]; cbn [POSTB] in PB.
- apply implM_ret. apply evt_done. exact PB.
- eapply (phaseC sp0 argv envp uid hw rnd TID s4 s5 s6 s7 s8 s9 s10 s11 VSP HCEIL HT RHF RBR FREE FWR TOW); [exact PB|].
intros DATA A cap cw L cfg sc s1 ms1 HC R0. rewrite HC.
exact (phaseDE sp0 argv envp uid hw rnd TID s4 s5 s6 s7 s8 s9 s10 s11 VSP HCEIL HT RBR FREE TRUN buf A cap DATA cw L cfg sc s1 ms1 R0).
Qed.

#[using="RHF RND RBD RBR MALLOC FREE FKP FPR FWX SWF FWR TOW TRUN RHI"] Theorem ref_main_proof : rmain_stmt.
Proof.
intros sp0 argv envp uid hw rnd F ms VSP VARGV VENVP MKF HCEIL HSEC HCAN AM.
destruct (Z.eq_dec (Z.of_nat (length argv)) 2) as [E2|NE2]; [| exact (main_usage sp0 argv envp uid hw rnd F VSP HCEIL HSEC HCAN VARGV VENVP RHI RHF FPR FWX SWF ms AM NE2)].
destruct argv as [|arg0 [|arg1 [|x l]]] eqn:EARGV; cbn in E2; try lia. rewrite <- EARGV in *.
eapply implM_mono with (Q := RQEXIT); [| intros code s' ms' H; exact H].
rewrite (main_model_eq argv arg0 arg1 EARGV).
eapply implM_evt.
{ eapply (main_to_P1 sp0 argv envp uid hw rnd F VSP HCEIL HSEC HCAN VARGV VENVP RHI RHF arg0 arg1); [exact EARGV| exact AM|].
intros TID ms' HT HP1. apply evt_done.
exact (main_from_P1 sp0 argv envp uid hw rnd F arg0 arg1 TID ms' VSP HCEIL VARGV VENVP EARGV HT MKF HP1). }
cbv beta. intros ms' H. exact H.
Qed.
End Main.
