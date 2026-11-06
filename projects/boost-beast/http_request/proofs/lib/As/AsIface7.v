(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition AOPDEL_ARR : Z := 0x0f0568.   (* [comment removed for export] *)
Definition ACWILD : Z := 2 ^ 22.          (* [comment removed for export] *)
Definition AWMAX  : Z := 7800.            (* [comment removed for export] *)

Section Iface7.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  #[local] Abbreviation SR := (as_SR H).      #[local] Abbreviation VIS := (as_VIS H).    #[local] Abbreviation AKREL := (as_AKREL H).
  #[local] Abbreviation MPRES := (as_MPRES H). #[local] Abbreviation RHEAP := (as_RHEAP H). #[local] Abbreviation AL := (as_AL H).
  #[local] Abbreviation Cf := (as_Cf H).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition opdel_arr_stmt : Prop := free_stmt_at H AOPDEL_ARR APC0_FREE.
  Definition opdel_arr_null_stmt : Prop := free_null_stmt_at H AOPDEL_ARR.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_wild_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (p : bptr) (n lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H),
      VIS s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ AKREL s' c /\ MPRES mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv]
      /\ as_rauxv_ok H m' B
      /\ apres H (as_lb_remove H p LB) (bv_unsigned sp) m m'
      /\ RHEAP s' (as_lb_remove H p LB) m'
      /\ ACONST m'
      /\ AL s' >= AL s - (Cf n + ACWILD).

  Definition free_wild_stmt_at (entry : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (mo : Model)
           (bs sbs : list byte),
      VIS s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      RHEAP s LB m -> AKREL s (mkCfg msF mo) -> In (p, A, n) LB -> Cf n + ACWILD <= AL s ->
      rw_cells asegs m A [CB (Z.to_nat n) bs] -> SHAD m A sbs -> Z.of_nat (length sbs) = nsh n ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 ->
      ACONST m ->
      bv_unsigned s0 <> bv_unsigned sp + 8 ->          (* [comment removed for export] *)
      a0 = Z_to_bv 64 A ->
      SR (free_wild_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p n lo B errv m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition asan_rt_hyps7 : Prop :=
       opdel_arr_stmt /\ opdel_arr_null_stmt
    /\ free_wild_stmt_at AFREE_STUB /\ free_wild_stmt_at AOPDEL /\ free_wild_stmt_at AOPDEL2 /\ free_wild_stmt_at AOPDEL_ARR.
End Iface7.
