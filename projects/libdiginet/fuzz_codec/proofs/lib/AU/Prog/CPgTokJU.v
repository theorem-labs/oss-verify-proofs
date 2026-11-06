(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: tok_branch_j, its soundness proof and the run pieces below are the text of
   lib/Reusable/YCbn.v (tok_branch :238-290, tok_branch_doml :1358-1371, tok_branch_sound :1181-1343, sym_run_tok /
   sym_run_to_tok / sym_runN_tok / sym_run_toN_tok :307-328, their doml and soundness lemmas :1388-1410,
   :1485-1595, :1613-1662) and of lib/Reusable/YCbq.v (SRr_run_tok_AJ / SRr_run_to_tok_AJ :2513-2546, aj_run_tok /
   aj_run_to_tok :3119-3166) and lib/A/Prog/CPgWalk.v (cw_run / cw_run_ob / cw_run_to), renamed with the suffix j
   (prefix cwj_ for the walk tactics) and run over the extended step sym_step_tokj. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgTokJ.v, with its module paths and module names changed; 6 of its 27 lines of code are new or changed and 611 lines of the source are left out. *)
(* The image-B forms of the walk tactics of lib/A/Prog/CPgTokJ.v: cwj_run / cwj_run_ob / cwj_run_to run that
   file's extended token engine (the instrumented check whose slow path lies behind a jump:
   lb t,(x >> 3)+SB ; beqz t,FAST ; j SLOW) on image B's code table (lib/AU/YCef.v tfibtbl_lib_ok) and shadow
   span (CPgWalkU's CW_Bspan). They take the arguments of CPgWalkU's cw_run / cw_run_ob / cw_run_to; an undecided
   branch is split with CPgWalkU's cw_branch as before. The engine, its soundness and the run tactics
   aj_run_tokj / aj_run_to_tokj do not depend on the image and are CPgTokJ's, used by Require. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CodecGlobs CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require CPgTokJ.
Import ListNotations.

Ltac cwj_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
CPgTokJ.aj_run_tokj tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [ .. | awr | idtac ] end.
Ltac cwj_run_ob awr obl :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
CPgTokJ.aj_run_tokj tfibtbl_lib_ok HS HJ SHOK CW_Bspan; [ obl .. | awr | idtac ] end.
Ltac cwj_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
CPgTokJ.aj_run_to_tokj tfibtbl_lib_ok HS HJ SHOK CW_Bspan stop; [ .. | awr | idtac ] end.
