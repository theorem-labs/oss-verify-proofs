(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's LLVMFuzzerTestOneInput - the jump table's arm 2 (op_drain), SECOND STAGE: the six calls, from
   `jal pthread_mutex_lock` (0x84900, the state DLK of lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v) to the arm's
   exit `j 84804` into the latch.  Proves no function (kind: segment walk - a segment of the entry function, its
   six callees taken as named contracts).

   Image: the pinned asan-ubsan objdump of fuzz_reply (fuzz_reply.objdump.txt sha256 17f5c434bf57; internal record),
   sha256 17f5c434bf5755fb1ceaed0ac3e631e85a2eae980ed9983d0ee03955bf5307ac.

   ------------------------------------------------------------------ the stretch this file walks (B's own code)
     0x848f4  auipc a0,0x554 ; addi s7,a0,1868      s7 = &g_lock (0x5d9040)          [stage 1's tail]
     0x848fc  mv a0,s7 ; jal 98dbc <pthread_mutex_lock>            ra = 0x84904 = BASE + A_dr_r1
     0x84904  mv a0,s6 ; jal 83278 <drain>                         ra = 0x8490c = BASE + A_dr_r2
     0x8490c  mv a0,s7 ; li s7,1 ; jal 992a8 <pthread_mutex_unlock> ra = 0x84918 = BASE + A_dr_r3
     0x84918  mv a0,s5 ; jal 85dd4 <check_no_loss_read>            ra = 0x84920 = BASE + A_dr_r4
     0x84920  addi a1,s1,192 ; mv a0,s5 ; jal 85e3c <check_no_loss> ra = 0x8492c = BASE + A_dr_r5
     0x8492c  ld a0,192(s1) ; jal 85a5c <check_shape_done>         ra = 0x84934 = BASE + A_dr_r6
     0x84934  j 84804                                              the latch, AF_LLVM_latch
   NO TRAP BRANCH lies on this stretch (the arm's three UBSan traps 0x8489c, 0x848a4, 0x848d4 are all in stage 1),
   so no `trap_<shape>` lemma of lib/B/W_traps.v is cited here and the runner decides every branch it meets.

   ------------------------------------------------------------------ what this walk carries, and B's differences
   from image A's twin lib/A/W_LLVMFuzzerTestOneInput_drain.v (a86c2788a94, dc_stA..dc_stF / dc_calls), whose
   structure this file ports:
     - &g_lock lives in s7 (reg 23), not in the frame cell F+40: dc_regs carries `getr regs 23 = w64 s7v` with
       s7v = rg_lock fr_RG before 0x84910 and s7v = 1 after it (`li s7,1`), which is what lregs_common asks of
       reg 23 at the latch.  There is no `sv8 (F+40) (rg_lock fr_RG)` conjunct anywhere.
     - B's aframe_at has no `full` flag, and lcut carries one more conjunct, `sv8 W mem (FF + 120)
       (flag_addr ly 1 fpos)`, a byte range of the owned class-1 fake frame: it rides the same keeper as the fake
       frame's 128 bytes.
     - the arm has no join block: 0x84934 jumps straight to the latch, s9 (= t, reg 25) and s4 (= the cursor,
       reg 20) are never reloaded, so dc_stF lands on INV_K itself.
     - check_no_loss is the kit's cnl_spec, lib/B/W_contract.v:2054 (cnl_post :1967, CNL_STK :1966 = 16640,
       Section w3n), taken at G = [(HA + 64, 32)], the drained slot's two list headers.
     - drain's aothers_at compares the fds modulo 2 ^ 32 (lib/B/W_contract.v:969, the machine's `beq a1,a4`),
       where image A compares them outright.
     - ablocks_sep's second clause is over the block's REQUEST size already (lib/B/W_LLVMFuzzerTestOneInput_cut.v
       :412-416), so no widening step (image A's FP_REQ) appears at the two calls that name a footprint.

   Every address, frame cell, register, global and shadow fact below is B's own.  The interface this file builds
   on is lib/B/W_LLVMFuzzerTestOneInput_drain_defs.v (the arm's addresses, DLK, dr_env and the model notions);
   the arm's first stage (0x8489c-0x84900) and the closing file are other lanes'. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_LLVMFuzzerTestOneInput_drain_calls.v, with its module paths and module names changed; 13 of its 51 lines of code are new or changed and 3361 lines of the source are left out. *)
(* proves no function (kind: segment lemma): the gone arm's model notions and its three LS-side obligation texts at
   image B, for the v3 LS layer's gone half; cited from lib/B/W_LLVMFuzzerTestOneInput_gone_base.v, not copied *)
(* The image-B (fuzz_reply.asan-ubsan) port of lib/A/ReplyLS3cTopxDefs.v (sha256
   4012d84d8b61; internal record) at 1318828167d3, row G-BLS3-port (the gone half).
   A's file COPIES the gone arm's model notions and the texts GN_LS_rig / GN_RI_step / GN_RI_end from the integration's
   lib/A/W_LLVMFuzzerTestOneInput_gone_base.v (a working branch bb9dae5d905), which A's tree did not have.
   Image B has its own gone_base (lib/B/W_LLVMFuzzerTestOneInput_gone_base.v, sha256 ee4640813df8 (internal record) at aa2172009cc9), so
   this file copies NOTHING: it re-exports B's gone_base, and every name of A's file is the gone_base name of the same
   spelling (A's names kept; the owners' rule for this port: cite B's gone_base, never copy it).
   Same text as A's copy (comments removed and whitespace collapsed, compared by a script on 2026-10-30), B gone_base
   lines: gn_more gn_id gn_kq (:361-363), gn_e0 gn_hj0 gn_q0 (:394-396), gn_pre (:416-417), gn_setn gn_set
   (:419-427), gn_pair_ok gn_pairs (:429-438), gn_after_rig (:440-448), gn_entry_model gn_rig_ok (:450-459), gn_cnl_ok
   (:461-466), gn_cshe_ok (:468-478), gn_at1 (:480-481), gn_run and its constructors (:483-495), GN_LS_rig (:594-600).
   NOT the same text (B's gone_base has a later text than A's copy; each is B's text here):
   - GN_RI_step (B :552-580; A's copy A :145-168): B binds (lyx : alayout) before Sx; B adds the premises
     `gn_op cx t m` and the relay entries' Forall (re_U and every key text NUL-free, 14 <= |key| <= APARTIAL) after
     `RINV cx t m`, and the block tie `(forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++
     rest) -> Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest))` after `mo_le MT S Sx cst`;
     B writes `AREC * capb (hs_held h) (hs_expected h)` where A writes capb's body inline (lib/B/W_contract.v :1961,
     equal by delta).
   - GN_RI_end (B :581-593; A's copy A :170-175): B adds `gn_op cx t m`, the same Forall and
     `(lm_gn m = 0 \/ lm_gn m = 1)` after `RINV cx t m`, and the same block tie after `mo_le MT S Sx cst`.
   Both B texts are image A's gone_base texts at d3a30b1562c6, the A text before A's REQ1-REQ5.
   Arguments: A's copies take MT LS RINV (MMAX) (A's Section gcopy).  B's Section g declares B first, so the two
   texts that read B are `GN_RI_step B MT LS RINV MMAX` and `GN_RI_end B MT LS RINV`; `GN_LS_rig MT LS RINV MMAX`
   reads no B and takes A's arguments.  The Checks at the end state these three applications.
   The Require header is B's gone_base's (lib/A AB1v -> lib/B YB1v; Reusable YE01 + lib/A AE2k -> lib/B YE01 YE2k;
   lib/A ACfn -> lib/B YCfn, Required only; lib/A W_* -> lib/B W_*; then ReplyGuardB). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  relay_remove_b_c relay_instance_gone_b_c gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Export W_LLVMFuzzerTestOneInput_gone_base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the three obligation texts as top_x applies them (A's header :9-11), at B's argument order *)
Section gcite.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.
Check (GN_LS_rig MT LS RINV MMAX : Prop).
Check (GN_RI_step B MT LS RINV MMAX : Prop).
Check (GN_RI_end B MT LS RINV : Prop).
End gcite.
Print Assumptions GN_LS_rig.
Print Assumptions GN_RI_step.
Print Assumptions GN_RI_end.
