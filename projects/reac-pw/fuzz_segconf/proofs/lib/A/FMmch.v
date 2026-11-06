(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSstrlen.v, with its module paths changed; 142 of its 194 lines of code are new or changed and 691 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed, no other change. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/RT_mem_bz.v, with its module paths changed; 18 of its 45 lines of code are new or changed and 167 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMmch.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* 2026-10-29: the A/Prog modules this file names are our lib/A/Prog/RtG_<name>.v (the walks relocated for this image); fm's names re-pointed. *)
(* Port-from: proofs/omx-clap-core/fuzz_state/lib/A/FSsl.v.
   Changes (2026-10-29): module path fuzz_state -> fuzz_reply; 4 fuzz_state.asan address numerals moved to fuzz_reply.asan, each paired by code (instruction by instruction, relocation fields masked) or, for a data cell, by the instruction that loads it (table: lib/A/RT_kit.v); renamed from FSsl.v. *)
(* Port-from: proofs/plugin-hostd/fuzz_reply/lib/A/Prog/wrap_kit.v:39-68
   (bz_mem_inv_same, sl_proof, mch_proof) and lib/A/Prog/asan_memcpy.v:42-50 (msteps_to_bz, evt_to_bz, mem_inv_of_bz).
   Changes (2026-10-28): restated without AsanRT / AsanRTFacts / BzBridge; the module aliases BzE / BzM / BzI
   (the shared ASan runtime proofs' BzBridge.v:15-17) and BzU / SLc / SLp / MHc / MHp (wrap_kit.v:22-27) are local; proofs unchanged. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_manifest.asan; from proofs/plugin-hostd/fuzz_reply/lib/A/FRsl.v, module path fuzz_reply -> fuzz_manifest, renamed FRsl.v -> FMmch.v, the strlen half (sl_proof, Prog/strlen_c, Prog/strlen) dropped, no address numerals (the musl memchr walk it wraps is fm's lib/A/Prog/memchr.v, MEMCHR 0x924a8, taken by path). *)
(* What it gives: musl memchr at 0x924a8 (fuzz_manifest.asan), the REAL(memchr) of the memchr interceptor, in the words
   of the Bz tree (I_musl.v memchr_stmt), which the interceptor walk takes as its section hypothesis MCH
   (Bz/A/I_memchrw.v) and the strnlen interceptor walk passes on (Bz/A/I_strnlen.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import Img0.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.RtG_memchr_c.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.RtG_memchr.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_musl.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.Mem.
Module BzI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib.ImageA.
Module BzU := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A.I_musl.
Module MHc := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.RtG_memchr_c.
Module MHp := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog.RtG_memchr.

(* Runs and memory facts in the Bz tree's words, from lib/Lib's (same image, same memory). *)

Lemma msteps_to_bz : forall s s', msteps rsegs s s' -> BzE.msteps BzI.asegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH].
  - apply BzE.msteps_refl.
  - eapply BzE.msteps_cons; [exact Hs | exact IH].
Qed.

Lemma evt_to_bz : forall (Q : machine_state -> Prop) ms, evt rsegs Q ms -> BzE.evt BzI.asegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [exact (msteps_to_bz ms ms' H) | exact HQ].
Qed.

Lemma mem_inv_of_bz : forall m, BzM.mem_inv BzI.asegs m -> mem_inv rsegs m.
Proof. intros m H a b E. exact (BzM.mem_inv_ro BzI.asegs m a b H E). Qed.

Lemma bz_mem_inv_same : forall m m', BzM.mem_inv BzI.asegs m -> munch [] m m' -> BzM.mem_inv BzI.asegs m'.
Proof. intros m m' H MU a. unfold BzM.mem_ok_at. rewrite (MU a I). exact (H a). Qed.

(* musl memchr (0x924a8), which the memchr interceptor calls through REAL(memchr) *)
Lemma mch_proof : BzU.memchr_stmt.
Proof.
  unfold BzU.memchr_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m buf
    BUF OK MI.
  apply evt_to_bz.
  apply (evt_mono rsegs (MHc.memchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 buf m)).
  - exact (MHp.memchr_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m buf BUF OK (mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ & B).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact (bz_mem_inv_same m m' MI MU) | exact B].
Qed.
