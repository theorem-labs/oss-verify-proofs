(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nest_frame (st : mstate) (g p : aptr) (j0 j1 : list byte) (raw : word) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 (conc st p)); C8 (Z_to_bv 64 (conc st g)); C8 (Z_to_bv 64 CTX); CB 40 j1; C8 raw].

Definition nest_call_post (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (raw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 j1 m',
    ms' = MS (mkR (Z_to_bv 64 0x15db0) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15a6c) fc None m' (seg_rom asegs)
    /\ pres_except (free_fp st lo (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) (nest_frame st g p j0 j1 raw)
    /\ mrep st' m'.
