(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (atime_stmt's vdso_func premise is vf = hvdso or P_cgt_init, and atime_post's vdso_func cell holds hvdso, the vDSO's clock_gettime entry, not 0; ATIME_STACK's bound is recomputed and stays 8192). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX ECH_AImg ECH_Iface AsAuxv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* time()'s stack at LPS 727298f3, read from the disassembly: P_time is a [j] to the ASan
   interceptor (frame 0x7f0 + 0x70 = 2144; its init test's frame, 16, is a sibling call), which
   calls musl's time (48), which calls clock_gettime (32).  The first call goes on to cgt_init (32),
   __vdsosym (112) and the strcmp interceptor (2208 with its init test): 4576 in all.  Every call
   enters the vDSO at clock_gettime's sp (cgt_init tail-calls it with its frame released), whose
   frame is F = [Vdso.vi_frame] = 240 (Vdso.v:314): 2144 + 48 + 32 + 240 = 2464.  8192 covers both. *)
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
      /\ rw_cells asegs m' A_vdso_func [C8 (Z_to_bv 64 hvdso)].

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
      rw_cells asegs m A_vdso_func [C8 (Z_to_bv 64 vf)] -> (vf = hvdso \/ vf = P_cgt_init) ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (atime_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo B errv m mo) (mkCfg msF mo).

  Definition atime_stmt : Prop := atime_stmt_at P_time ATIME_STACK.
End HCW.
