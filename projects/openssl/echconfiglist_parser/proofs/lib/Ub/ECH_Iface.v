(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition FUZZ_STACK : Z := 16384.
(* [comment removed for export] *)
Definition FUZZ_LIVE : Z := 2^24.
Definition TRANS_CNT : Z := 1024.
Definition LIB_CNT_MAX : Z := 1800.
Definition LIB_BYTES_MAX : Z := 2^17.
(* [comment removed for export] *)
Definition TRANS_BIG : Z := 8.
Definition LIB_BIG_MAX : Z := 2.
Definition fuzz_cnt (st : libst) : Z := (if is_fresh st then LIB_CNT_MAX else 0) + TRANS_CNT.
Definition fuzz_live (st : libst) : Z := (if is_fresh st then LIB_BYTES_MAX else 0) + FUZZ_LIVE.
Definition fuzz_big (st : libst) : Z := (if is_fresh st then LIB_BIG_MAX else 0) + TRANS_BIG.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section W.
  Variable H : hsr.

  Definition fuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LIB LBc : list block) (st : libst) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LIB' LBc' : list block) (st' : libst),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv usegs m' /\ relro_lib m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (LIB' ++ LBc') m' /\ Permutation LBc' LBc
      /\ LIBST st' LIB' m' /\ is_fresh st' = false
      /\ Z.of_nat (length LIB') <= LIB_CNT_MAX /\ lb_bytes LIB' <= LIB_BYTES_MAX /\ lb_big LIB' <= LIB_BIG_MAX
      /\ (is_fresh st = false -> LIB' = LIB)
      /\ xpres LBc (bv_unsigned sp) LIBX m m'.

  Definition fuzz_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
           (s : PState) (LIB LBc : list block) (st : libst) (D N lo B : Z) (ds : list byte) (errv : word),
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N ->
      (* [comment removed for export] *)
      bytes_at usegs m D ds -> Z.of_nat (length ds) = N -> N < 2^26 -> D mod 16 = 0 ->
      (1 <= N -> exists pD, In (pD, D, N) LBc) -> (N = 0 -> D = P_FUZZ_EMPTY) ->
      (* [comment removed for export] *)
      hs_RHEAP H s (LIB ++ LBc) m -> hs_KREL H s mo -> LIBST st LIB m ->
      lb_bytes (LIB ++ LBc) + fuzz_live st <= hs_LIVE_MAX H ->
      Z.of_nat (length (LIB ++ LBc)) + fuzz_cnt st <= hs_LIVE_CNT_MAX H ->
      lb_big (LIB ++ LBc) + fuzz_big st <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->
      (* [comment removed for export] *)
      bv_unsigned sp mod 16 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - FUZZ_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> relro_lib m -> tp = Z_to_bv 64 RATP ->
      bv_unsigned ra mod 2 = 0 ->
      hs_SR H (fuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LBc st lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_FUZZ_ENTRY) fc None m (seg_rom usegs)) mo).
End W.

End HCW.
