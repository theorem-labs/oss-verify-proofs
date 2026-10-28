(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX ECH_AImg ECH_Iface AsAuxv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ATIME_STACK : Z := 8192.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition atime_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 (tv : word) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      as_VIS H s (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B /\ aauxv_ok m' B /\ as_RHEAP H s LB m'
      /\ munch [(bv_unsigned sp - ATIME_STACK, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8); (errno_addr tp, errno_addr tp + 4)]%Z m m'
      /\ wmono asegs m m'
      /\ rw_cells asegs m' A_vdso_func [C8 (Z_to_bv 64 0)].

  (* [comment removed for export] *)
  Definition atime_stmt_at (entry stack : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block)
           (lo B vf : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 0 ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m B -> aauxv_ok m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - stack ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> arelro_lib m ->
      rw_cells asegs m A_vdso_func [C8 (Z_to_bv 64 vf)] -> (vf = 0 \/ vf = P_cgt_init) ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (atime_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo) (mkCfg msF mo).

  Definition atime_stmt : Prop := atime_stmt_at P_time ATIME_STACK.
End HCW.
