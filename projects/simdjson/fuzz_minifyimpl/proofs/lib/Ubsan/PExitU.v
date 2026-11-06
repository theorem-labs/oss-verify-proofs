(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep MonadX Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import Stdio_pure DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit UImg PExitU_defs PIosX_iface PIosX_musl F_stdio_exit PExitU_tail PExitU_head1 PExitU_headG PExitU_head2.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface PAtexit_cells PU_iface PStartU RDriver_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Malloc Monad Stdio Driver HarnessM PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma client_exit_none : forall {B} (s : PState) (K : Monad.M PState B), ps_fa s = None -> (ProgP.client_exit ;;; K) s = K s.
Proof. intros B s K H. unfold ProgP.client_exit, HarnessM.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.
Lemma client_exit_some : forall {B} (s : PState) p (K : Monad.M PState B), ps_fa s = Some p ->
  (ProgP.client_exit ;;; K) s = ((HarnessM.opdelete raw_free p ;;; mupd (set_fa_ps None)) ;;; K) s.
Proof. intros B s p K H. unfold ProgP.client_exit, HarnessM.client_exit, mbind, mget, mret. cbn. rewrite H. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
Theorem pexitU_proof : opdelete_stmt ->
  forall code (s : PState) ms (Q : Empty_set -> PState -> machine_state -> Prop),
    pat_exitU code s ms -> implM usegs (ProgP.client_exit ;;; Driver.exit_model ProgP.io code) s Q ms.
Proof.
  intros OPD code s ms Q H.
  destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t & AB &
                 td0 & td1 & td2 & td3 & errv & dso & LB & -> & H).
  destruct H as (ST & TID & EXL & GF & FA & FINZ & GCX & DSO & OFL & SIN & SINF & SOU & SEU & SOF & SEF & IOS & RH & CS & INCB & AUX & SPAB & ERR & MI
                 & Htp & Ha0 & Ht & LO & ATL & GLO & AL & SP47).
  unfold pincb in INCB.
  unfold PEXITU_STACK in LO. unfold PEXIT. unfold RERRNO in ERR.
  pose proof (RHEAP_need_locks _ _ _ RH) as LIBC. unfold RNEED_LOCKS, b8 in LIBC.
  pose proof (RHEAP_ssp _ _ _ RH) as (GG & GU).
  pose proof (stdio_exit_proof_id) as SE.
  pose proof wcrtomb0_proof as WCR. pose proof fwrite0_out_proof as FW0. pose proof fwrite0_err_proof as FW0E. pose proof fflush_err_proof as FFLE.
  assert (FFL : fflush_out_stmt ps_so set_so_ps).
  { apply fflush_out_proof; [intros s' so; reflexivity | intros s' so so'; reflexivity | intros [mm b f so]; reflexivity]. }
  assert (FFLS : fflush_out_stmt (St := stdout_st) (fun so => so) (fun so _ => so)) by (apply fflush_out_proof; reflexivity).
  destruct CS as [[CIMG CS]|[EFA0 CS0]].
  - (* [comment removed for export] *)
    destruct (ps_fa s) as [p|] eqn:EFA.
    + (* [comment removed for export] *)
      destruct CS as (V & INB & VCELL & GUARD1 & VEC & FBK & (AT0 & AT1 & AT1b & AT2 & AT2b)). unfold PCALL_THUNK, PAEF_GUARD in AT1, AT2.
      unfold implM. rewrite (client_exit_some s p _ EFA).
      fold (implM usegs ((HarnessM.opdelete raw_free p ;;; mupd (set_fa_ps None)) ;;; exit_model ProgP.io code) s Q).
      eapply (exit_head2_spec SE WCR FW0 FW0E FFL FFLS FFLE OPD s Q) with (lo := lo) (t := t) (AB := AB) (LB := LB) (V := V) (errv := errv);
        try first [ eassumption | reflexivity | exact SP47 | (clear - LO; lia)
                  | (unfold PVEC in VEC; exact VEC)
                  | (unfold RSTDIN; exact SIN) | (unfold RSTDIN, stdin_cells; exact SINF)
                  | (unfold PDTOR_THUNK in AT1b; exact AT1b) | (unfold PVEC in AT2b; exact AT2b) ].
    + (* [comment removed for export] *)
      destruct CS as (_ & (AT0 & AT1 & AT1b & AT2 & AT2b)). unfold PCALL_THUNK, PAEF_GUARD in AT1, AT2.
      unfold implM. rewrite (client_exit_none s _ EFA). change ProgP.io with (io_S ps_so set_so_ps).
      fold (implM usegs (Driver.exit_model (io_S ps_so set_so_ps) code) s Q).
      eapply (exit_headG_spec ps_so set_so_ps SE WCR FW0 FW0E FFL FFLS FFLE s Q) with (lo := lo) (t := t) (so_x := ps_so s) (guard := CAN);
        try first [ eassumption | reflexivity | (intros _; reflexivity) | exact GLO | exact SP47
                  | (unfold EXIT_TAIL_DEPTH; clear - LO; lia)
                  | (unfold RSTDIN; exact SIN) | (unfold RSTDIN, stdin_cells; exact SINF)
                  | (unfold got_ssp, ssp_guard; first [exact GG | exact GU]) ].
  - (* [comment removed for export] *)
    destruct CS0 as (_ & _ & (AT0 & AT1 & AT1b & AT2 & AT2b)).
    unfold implM. rewrite (client_exit_none s _ EFA0). change ProgP.io with (io_S ps_so set_so_ps).
    fold (implM usegs (Driver.exit_model (io_S ps_so set_so_ps) code) s Q).
    eapply (exit_head1_spec ps_so set_so_ps SE WCR FW0 FW0E FFL FFLS FFLE s Q) with (lo := lo) (t := t) (so_x := ps_so s) (guard := CAN);
      try first [ eassumption | reflexivity | (intros _; reflexivity) | exact GLO | exact SP47
                | (unfold EXIT_TAIL_DEPTH; clear - LO; lia)
                | (unfold RSTDIN; exact SIN) | (unfold RSTDIN, stdin_cells; exact SINF)
                | (unfold got_ssp, ssp_guard; first [exact GG | exact GU]) ].
Qed.
End CANSEC1.
