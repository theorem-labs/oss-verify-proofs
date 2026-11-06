(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Prog/wrap_kit.v:39-68
   (bz_mem_inv_same, sl_proof, mch_proof) and lib/A/Prog/asan_memcpy.v:42-50 (msteps_to_bz, evt_to_bz, mem_inv_of_bz).
   Changes (a Theorem Labs lane, 2026-10-28): restated without AsanRT / AsanRTFacts / BzBridge; the module aliases BzE / BzM / BzI
   (a Theorem Labs lane's BzBridge.v:15-17) and BzU / SLc / SLp / MHc / MHp (wrap_kit.v:22-27) are local; proofs unchanged.
   The musl strlen walk sl_proof uses is a Theorem Labs lane's, taken by path from the same commit, unchanged:
   lib/A/R_strlen.v (strlen_spec), lib/A/Prog/strlen_c.v (strlen_contract), lib/A/Prog/strlen.v (strlen_holds),
   lib/A/Img0.v (rsegs = the fs.asan image). Their Require closure (35 files) has no AsanRT, asan_cells, Admitted or Axiom.
   The musl memchr walk mch_proof uses, the same way: lib/A/R_memchr.v, lib/A/Prog/memchr.v, lib/A/Prog/memchr_c.v,
   lib/A/Spec/StrFun.v, lib/A/Ox/F80_001.v .. F80_003.v (absent here; the other 32 files of their 39-file closure are
   byte-identical in this tree; no AsanRT, asan_cells, Admitted or Axiom).
   What it gives: the plain strlen at 0x99070 and the plain memchr at 0x98924, in the words of the Bz tree
   (I_musl.v strlen_stmt / memchr_stmt), which the interceptor walks take as their section hypotheses SL
   (Bz/A/I_strlen.v:96) and MCH (Bz/A/I_memchrw.v:77). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import Img0.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.strlen_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.strlen.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.memchr_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.memchr.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_musl.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.Mem.
Module BzI := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.Lib.ImageA.
Module BzU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Bz.A.I_musl.
Module SLc := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.strlen_c.
Module SLp := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.strlen.
Module MHc := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.memchr_c.
Module MHp := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog.memchr.

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

(* the plain strlen (0x99070) the strlen interceptor calls through REAL(strlen) *)
Lemma sl_proof : BzU.strlen_stmt.
Proof.
  unfold BzU.strlen_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack
    BUF NZ PAD MI.
  apply evt_to_bz.
  apply (evt_mono rsegs (SLc.strlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack m)).
  - exact (SLp.strlen_holds ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m str slack BUF NZ PAD (mem_inv_of_bz m MI)).
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & _ & B).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact (bz_mem_inv_same m m' MI MU) | exact B].
Qed.

(* the plain memchr (0x98924) the memchr interceptor calls through REAL(memchr) *)
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
