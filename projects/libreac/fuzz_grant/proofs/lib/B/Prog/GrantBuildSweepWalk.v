(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_grant_build_sweep's contract, adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v (the entry state and its region_ok facts), lib/A/AChf.v (the side-stack frame: aj_stack_malloc_atS, the realigned sp, reseat, the frame and shadow regions, the shadow_decl_ok alias), lib/A/ACb8.v (the chain pushed at a call, the flag store and the return) and lib/A/ACh1.v (a callee in afn_pre form through cl_callS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantBuildSweepWalk.v at a working branch eacc832ec38a (blob 34c52c812f2, the blob the walk was ported from): the walk theorem of reac_grant_build_sweep (0x855fc), stated as GrantBContracts.v's walk_reac_grant_build_sweep. It composes the four parts of the walk: GrantBuildSweep.v the entry, the frame, the early exits and the loop (bs_main, pb_bs_head, pb_bs_loop); GrantBuildSweepCell.v one cell of the loop, with the call of reac_headamp_tx_effective (pb_bs_cell); GrantBuildSweepTail.v from the loop's end through reac_ctrl_build_grant_sweep to the return (pb_bs_tail); GrantBuildSweepLib.v the cut states and facts they share. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC4b YC81 YC88 YCbw YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantSyms GrantList GrantAddr GrantTop GrantPa GrantPaLib GrantFrame GrantRo.
(* The parts are Required, not Imported: each has its own local lemma and tactic names. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require
GrantBContracts GrantBuildSweepLib GrantBuildSweep GrantBuildSweepCell GrantBuildSweepTail.
Module C := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantBContracts.
Module L := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantBuildSweepLib.
Module M := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantBuildSweep.
Module K := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantBuildSweepCell.
Module T := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantBuildSweepTail.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg grant_listing}.
Variable B : asyms.
Theorem pb_reac_grant_build_sweep : C.walk_reac_grant_build_sweep B.
Proof.
unfold C.walk_reac_grant_build_sweep, C.hyps_reac_grant_build_sweep,
C.RT_LAWS, C.RT_PALIB, C.RT_PALIBF, C.RT_ML, C.RT_SM, C.RT_SMP, C.RT_ASF, C.RT_FFL.
intros (HL & HPL & HPLF & HML & HSM & HSMP & HASF & HFFL & _) TEFF TBGS.
(* The callee's contract TBGS is GrantBContracts.v's, whose tcj_kept is guarded by bgs_ok as image A's: it is
   image A's form (T.tbgs_post_g) word for word, and that gives the -1 path's keep clause. *)
assert (KEEP : T.tbgs_spec_with B (T.tbgs_post_keep B))
  by (apply T.tbgs_keep_of_g; exact (T.tbgs_spec_with_C B TBGS)).
assert (CELL : L.bs_cell_spec B) by (apply K.pb_bs_cell; assumption).
assert (TAIL : L.bs_tail_spec B) by (apply T.pb_bs_tail; assumption).
apply M.bs_main; assumption.
Qed.
End b.
