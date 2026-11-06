(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated by R4Printf.BzPrintfPort (a Theorem Labs lane) onto plugin-hostd/fuzz_reply.asan from a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/K/I_vfprintfw.v: module paths and 12 address numerals, rewritten in one pass, each paired by object (the code functions are identical modulo pc-relative fields): 0x1eb50->0x1eaab string "vfprintf" (code ref ___interceptor_vfprintf+0x4c addi); 0x42688->0x421d0 trampoline_vfprintf+0x0; 0x44fdc->0x45964 printf_common+0x0; 0x45aa4->0x4642c ___interceptor_vfprintf+0x0; 0x45af8->0x46480 ___interceptor_vfprintf+0x54; 0x45afc->0x46484 ___interceptor_vfprintf+0x58; 0x45b10->0x46498 ___interceptor_vfprintf+0x6c; 0x45b14->0x4649c ___interceptor_vfprintf+0x70; 0x5a078->0x5adf0 TryAsanInitFromRtl+0x0; 0x92d48->0x92d08 vfprintf+0x0; 0xa1468->0x9f768 REAL(vfprintf)+0x0; 0x5f7000->0x5fb000 try_init_spec's stack bound (our I_ikit.v), fuzz_reply image end. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/Bz/K/I_vfprintfw.v, with its module paths and addresses changed; 7 of its 37 lines of code are new or changed and 112 lines of the source are left out. *)
(* Image B twin of lib/A/Bz/K/I_vfprintfw1.v at d49bd1db505: lib/B/Bz/K/I_vfprintfw1.v at 3da0143047f (= 891ad39df4c) with its stack floor `0x5f7000 <= lo` (fuzz_state's image top) set to fuzz_reply.asan-ubsan's top 0x5fc000 (1x), as lib/A has fuzz_reply.asan's top 0x5fb000; every other numeral equals the A text's, moved by symbol + offset (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread X_atexit D_kit I_ikit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.K Require Import I_vprintfw I_vfprintfw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma vfprintf_walkA1n : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 64 -> 0x5fc000 <= lo -> usp <= 2^47 ->
  rw_cells asegs m 0xa7318 [C1 (Z_to_bv 8 1)] -> ro_cells asegs m 0x9df40 [C8 (Z_to_bv 64 0x138168)] ->
  ro_cells asegs m 0x1381bc [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (vfwA1_post usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42228) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH AI GCF CPF MI.
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
  carve_frame 48%nat ST. rename FR into FRv.
  apply (rw_cells_split_CB asegs _ _ [] 48 _ [] [8; 8; 8; 8; 8; 8]%nat) in FRv; [| reflexivity]. cbn [mk_CB_cells app] in FRv.
  xsteps_to 0x5ae48%Z.
  call try_init_spec; [exact AI | rewrite EU48; exact ST | rewrite EU48; lia | lia | assumption |].
  rename POST into ST. rewrite EU48 in ST.
  xsteps_to 0x459bc%Z.
  apply evt_done. unfold vfwA1_post. do 13 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST| exact FRv].
Qed.
