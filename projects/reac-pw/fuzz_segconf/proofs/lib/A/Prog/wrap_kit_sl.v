(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_mem_bz.v; 31 of its 62 lines of code are new or changed and 163 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/FRsl.v, with its module paths changed; 6 of its 30 lines of code are new or changed and 38 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import asan_memcpy_bz.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_musl.
Import ListNotations.
Open Scope Z_scope.

Module AMC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.asan_memcpy_bz.
Module BzU := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_musl.
Module SLc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen_c.
Module SLp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.strlen.

Lemma bz_mem_inv_same : forall m m', BzM.mem_inv BzI.asegs m -> munch [] m m' -> BzM.mem_inv BzI.asegs m'.
Proof. intros m m' H MU a. unfold BzM.mem_ok_at. rewrite (MU a I). exact (H a). Qed.

Lemma sl_proof : BzU.strlen_stmt.
Proof.
  unfold BzU.strlen_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack
    BUF NZ PAD MI.
  apply AMC.evt_to_bz.
  apply (evt_mono rsegs (SLc.strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)).
  - exact (SLp.strlen_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m str slack BUF NZ PAD (AMC.mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ & B).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact (bz_mem_inv_same m m' MI MU) | exact B].
Qed.
