(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_Iface
     ECH_C1_stmt ECH_C3_stmt ECH_C4_stmt ECH_C7_stmt ECH_C13_stmt ECH_C14_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition PARSE_CNT : Z := DECODE_CNT + ERRSTR_CNT + 8.           (* [comment removed for export] *)
Definition PARSE_BYTES : Z := DECODE_BYTES + ERRSTR_BYTES + 512.
Definition PARSE_BIG : Z := DECODE_BIG.
Definition PARSE_STACK (M : libmid) : Z := FR_parse_one + Z.max (READCFG_STACK M) (NEWMEMBUF_STACK (mid_ctx M)).

Section W.
  Variable H : hsr.

  Definition parse_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LIB LB : list block) (M : libmid) (D : Z) (ds : list byte) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (M' : libmid) (LBN : list block),
      let LB' := LBN ++ LB in                                        (* [comment removed for export] *)
      cfg_ms k = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model k) /\ hs_MPRES H mo (cfg_model k)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ (exists b, mid_ctx M' = CtxReady b)
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES /\ lb_big (mid_errblocks M') = 0
      /\ bytes_at rsegs m' D ds
      /\ xpres LB (bv_unsigned sp) (memflag_foot ++ CTX_X ++ ERR_X ++ VDSO_X ++ errph_foot (mid_err M)) m m'.   (* [comment removed for export] *)
  Definition parse_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LIB LB : list block)
           (M : libmid) (D N lo B : Z) (ds : list byte) (errv : word),
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N -> 0 <= N < 2^31 ->
      bytes_at rsegs m D ds -> zlength ds = N -> 0 < D -> D + N <= hceil ->
      (1 <= N -> exists pD, In (pD, D, N) LB /\ forall b, In b LIB -> blk_id b <> pD) ->            (* [comment removed for export] *)
      (N = 0 -> D = P_FUZZ_EMPTY) ->                                                                  (* [comment removed for export] *)
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) ->
      hs_RHEAP H s (mid_errblocks M ++ LB) m -> hs_KREL H s mo ->
      lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + PARSE_BYTES <= hs_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + PARSE_CNT <= hs_LIVE_CNT_MAX H ->
      lb_big (mid_errblocks M ++ LB) + mid_big M + PARSE_BIG <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - PARSE_STACK M ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP -> bv_unsigned ra mod 2 = 0 ->
      hs_SR H (parse_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB M D ds lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_parse_one) fc None m (seg_rom rsegs)) mo).

  (* [comment removed for export] *)
  Definition C15_stmts : Prop := parse_one_stmt /\ fuzz_stmt H.
End W.
End HCW.
