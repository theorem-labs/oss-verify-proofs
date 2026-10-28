(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition sdWd (cx : cctx) : list (Z * Z) :=
  [(c_E cx + 116, c_E cx + 120); (c_E cx + 640, c_E cx + 648); (c_A2 cx, c_A2 cx + ARR2_SIZE)].

Definition MUd (cx : cctx) (g : eg) (e : est) (usp : Z) (m0 : word -> option byte) (b : bw) (m : word -> option byte) : Prop :=
  rw_cells s0segs m (c_E cx) (EHEAD1 cx g (est_set_bw e b)) /\
  rw_cells s0segs m (c_E cx + 640) (EHEAD2 cx g (est_set_bw e b)) /\
  u8arr s0segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) b) ARR2_SIZE) /\
  u8arr s0segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\
  u8arr s0segs m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) /\
  u32arr s0segs m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) /\
  rw_cells s0segs m (usp + 1032) [C8 (Z_to_bv 64 (c_A1 cx))] /\
  mem_inv s0segs m /\
  munch (sdWd cx) m0 m /\ wmono s0segs m0 m.

End ACeilS1.

Ltac openMUd Gmtf Gbs Gzb H :=
  let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let MU := ident:(MU) in
  cps_destruct H as (?EH1 & ?EH2 & ?AR2 & ?AR1 & ?LEN & ?COD & ?STK & ?MI & ?MU & ?WM);
  unfold sdWd in MU;
  unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2;
  rewrite Gbs, Gmtf in EH2; rewrite Gzb, Gmtf in EH1.

Ltac closeMUd Gmtf Gbs Gzb :=
  split; [|split; [| repeat (split; [eassumption|]); eassumption]];
  [ unfold EHEAD1; cbn_est; rewrite Gzb, Gmtf; eassumption
  | unfold EHEAD2; cbn_est; rewrite Gbs, Gmtf; eassumption ].
