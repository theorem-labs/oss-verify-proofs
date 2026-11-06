(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr FP.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env Pm_iface Pm_iface2 RT_fk RT_fk_iface D_iface D_defs Bi_fktw Po_rows Po_iface Po_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition mod_msg : Z := e_makeOrientDecision + 0x50.    (* [comment removed for export] *)
Definition mod_ras : Z := e_makeOrientDecision + 0x88.    (* [comment removed for export] *)
Definition mod_ep : Z := e_makeOrientDecision + 0xe0.    (* [comment removed for export] *)
Definition mod_hd : Z := e_makeOrientDecision + 0xf4.    (* [comment removed for export] *)
Definition mod_s : Z := e_makeOrientDecision + 0x104.    (* [comment removed for export] *)
Definition mod_up : Z := e_makeOrientDecision + 0x10c.   (* [comment removed for export] *)
Definition mod_ln : Z := e_makeOrientDecision + 0x118.   (* [comment removed for export] *)
Definition mod_m2 : Z := e_makeOrientDecision + 0x120.   (* [comment removed for export] *)
Definition mod_m3 : Z := e_makeOrientDecision + 0x130.   (* [comment removed for export] *)
Definition mod_un : Z := e_makeOrientDecision + 0x140.   (* [comment removed for export] *)
Definition mod_lp : Z := e_makeOrientDecision + 0x14c.   (* [comment removed for export] *)
Definition mod_c1 : Z := e_makeOrientDecision + 0x150.   (* [comment removed for export] *)
Definition mod_c2 : Z := e_makeOrientDecision + 0x16c.   (* [comment removed for export] *)
Definition mod_c3 : Z := e_makeOrientDecision + 0x188.   (* [comment removed for export] *)
Definition mod_c4 : Z := e_makeOrientDecision + 0x1a4.   (* [comment removed for export] *)
Definition mod_st : Z := e_makeOrientDecision + 0x1b8.   (* [comment removed for export] *)
Definition mod_jn : Z := e_makeOrientDecision + 0x1c4.   (* [comment removed for export] *)

Definition MOD_STOPS : list Z := [e_lept_stderr; mod_hd; mod_jn].

Section ModDefs.
Variable RT : rt_sig.

Definition makeOrientDecision2_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (porient : Z) (upbits leftbits : Z) (x : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  reg_get F r_fa0 = fs32 upbits -> reg_get F r_fa1 = fs32 leftbits -> reg_get F r_fa2 = fs32 F_1_0 -> reg_get F r_fa3 = fs32 F_1_0 ->
  a0 = Z_to_bv 64 porient -> a1 = Z_to_bv 64 0 ->
  bv_unsigned sp <= porient -> porient + 4 <= USTACK_TOP - 16 -> porient mod 4 = 0 -> rw_cells asegs m porient [C4 x] ->
  lenv RT Σ m sp lo (LSTK 3) -> lres RT Σ 1 0 1 ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_makeOrientDecision m)))
    (fun c => exists (Σ' : rts RT) (o : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_stF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) F m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(porient, porient + 4)] m m'
          /\ rw_cells asegs m' porient [C4 (Z_to_bv 64 o)] /\ 0 <= o <= ORIENT_MAX) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 1 <= rt_credit RT Σ').

End ModDefs.
