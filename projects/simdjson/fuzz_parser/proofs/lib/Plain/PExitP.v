(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg F_syscalls StdioFiles Startup_A Exit F_stdio_exit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface PU_iface PStartU RDriver_iface RDriver_kit PlainImpl.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Malloc Monad Stdio Driver HarnessP PState ProgP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Lemma client_exit_seq : forall {B} (s : PState) (K : Monad.M PState B), (ProgP.client_exit ;;; K) s = K s.
Proof. intros B s K. unfold ProgP.client_exit, HarnessP.client_exit, mbind, mret. cbn. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
Theorem pexitP_proof : pexit_stmt.
Proof.
  intros code s ms Q H.
  destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 &
                 s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t & AB &
                 td0 & td1 & td2 & td3 & errv & dso & LB & -> & H).
  destruct H as (ST & TID & EXL & GF & FA & FINZ & GCX & DSO & OFL & SIN & SOU & SEU & SOF & SEF & IOS & RH & CS & XTT & XCB & AUX & SPAB & ERR & MI
                 & Htp & Ha0 & Ht & LO & ATL & GLO & AL & SP47).
  assert (TBL : Exit.pexit_tbl m).
  { unfold pincb in XCB. destruct XTT as [(T0 & T1 & T2)|(T0 & T1 & T2)];
      [left; exact (conj T0 (conj T1 T2))| right; exact (conj T0 (conj T1 (conj T2 XCB)))]. }
  unfold PEXITU_STACK in LO. unfold PEXIT.
  destruct (RHEAP_libc_head _ _ _ RH) as (cdt & thr & sec & tm1 & LCH).
  pose proof (RHEAP_ssp _ _ _ RH) as (GG & GU).
  unfold implM. rewrite (client_exit_seq s). change ProgP.io with (io_S ps_so set_so_ps).
  fold (implM psegs (Driver.exit_model (io_S ps_so set_so_ps) code) s Q).
  eapply (Exit.exit_spec ps_so set_so_ps stdio_exit_proof_ps s Q) with (lo := lo) (t := t) (guard := CAN);
    try first [ eassumption | reflexivity | exact SP47 | (clear - LO; lia) | exact GLO ].
Qed.
End CANSEC1.
