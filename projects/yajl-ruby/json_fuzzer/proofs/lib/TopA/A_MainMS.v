(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr Nodes NodesCfg InitMem RunInit Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_base ADrv_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

Section RC__1.
Context {RC__ : RunCeiling}.
#[local] Notation gpv := (Z_to_bv 64 0x10800).
#[local] Notation tpv := (Z_to_bv 64 0x5e0b10).
(* [comment removed for export] *)
Definition main_ms (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (FULL : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    ms = MS (mkR (Z_to_bv 64 0x91610) (Z_to_bv 64 (bv_unsigned sp0 + -48)) gpv tpv t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp0 + 8)) (Z_to_bv 64 (argc argv))
                 (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 0x81aa4) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x81aa4) fc None FULL (seg_rom asegs)
    /\ stk asegs FULL (LO sp0) (bv_unsigned sp0 + -48) /\ mem_inv asegs FULL /\ AIMG sp0 argv envp uid hw rnd FULL /\ ASTAT FULL /\ frm0 fc.
End RC__1.
