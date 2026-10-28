(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 AsAuxv ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
     ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C7 ECH_AStmt_C13 ECH_AStmt_C9 ECH_AStmt_C14.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition PARSE_CNT : Z := DECODE_CNT + ERRSTR_CNT + 8.           (* [comment removed for export] *)
Definition PARSE_BYTES : Z := DECODE_BYTES + ERRSTR_BYTES + 512.
(* [comment removed for export] *)
Definition PARSE_STACK (M : libmid) : Z :=
  FR_parse_one + Z.max (READCFG_STACK M) (Z.max (NEWMEMBUF_STACK (mid_ctx M)) (Z.max STORENEW_STACK (Z.max STOREFREE_STACK BIOFREE_STACK))).
(* [comment removed for export] *)
Definition PARSE_LF : nat := READCFG_LF.

(* [comment removed for export] *)
Definition R_parse_one_OSSL_ECHSTORE_new : Z := 0x1ef434.
Definition R_parse_one_BIO_new_mem_buf : Z := 0x1ef44c.
Definition R_parse_one_OSSL_ECHSTORE_read_echconfiglist : Z := 0x1ef464.
Definition R_parse_one_OSSL_ECHSTORE_free : Z := 0x1ef470.

(* [comment removed for export] *)
Definition mid_after_nmb (M : libmid) (x : ctxinfo) : libmid := mkMID 1 (CtxReady x) (mid_err M) (mid_E M) (mid_vdso M).

Section W.
  Variable H : asr.
  Section RC.
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition PFC_parse (M : libmid) (x : ctxinfo) : list (Z * list Z) :=
       pf_shift R_parse_one_BIO_new_mem_buf (PF_newmembuf (mid_ctx M))
    ++ pf_shift R_parse_one_OSSL_ECHSTORE_read_echconfiglist (PF_readcfg PF9new PF9free (mid_after_nmb M x))
    ++ pf_shift R_parse_one_OSSL_ECHSTORE_free PF_storefree.
  Definition parse_closed_ok (M : libmid) : Prop :=
    forall x, Forall (fun r : Z * list Z => trace_ok (as_TR H) (fst r) (snd r)) (PFC_parse M x).

  (* [comment removed for export] *)
  Definition PARSE_COST (M : libmid) : Z :=
    as_Cm H STORE_SIZE + NEWMEMBUF_COST H (mid_ctx M) + READCFG_COST H M + as_Cf H (STORE_SIZE + DECODE_BYTES) + BIOFREE_COST H.

  Definition parse_one_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LIB LB : list block) (LF : list fframe) (M : libmid) (D N : Z) (ds : list byte) (lo B shi : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (M' : libmid) (LBN : list block) (XS : list (Z * Z)),
      let LB' := LBN ++ LB in                                        (* [comment removed for export] *)
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ mem_inv asegs m' /\ ACONST m' /\ arelro_lib m' /\ stk asegs m' lo (bv_unsigned sp) /\ stack0 m' lo shi
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ (exists b, mid_ctx M' = CtxReady b)
      (* [comment removed for export] *)
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES
      /\ bytes_at asegs m' D ds /\ (1 <= N -> addressable m' D N)
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m'                                                        (* [comment removed for export] *)
      /\ xpres H LB (bv_unsigned sp) (memflag_foot ++ CTX_X ++ ERR_XE ++ VDSO_X ++ errph_foot (mid_err M) ++ XS) m m'   (* [comment removed for export] *)
      /\ as_AL H s' >= as_AL H s - PARSE_COST M.
  Definition parse_one_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
           (M : libmid) (D N lo B shi : Z) (ds : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_parse_one) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N -> 0 <= N < 2^31 ->
      bytes_at asegs m D ds -> zlength ds = N -> 0 < D -> D + N <= aceil ->
      (1 <= N -> exists pD, In (pD, D, N) LB /\ forall b, In b LIB -> blk_id b <> pD) ->            (* [comment removed for export] *)
      (N = 0 -> D = P_FUZZ_EMPTY) ->                                                                  (* [comment removed for export] *)
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_closed_ok H M -> ctxph_closed_ok H (mid_ctx M) ->   (* [comment removed for export] *)
      as_RHEAP H s (mid_errblocks M ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + PARSE_BYTES <= as_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + PARSE_CNT <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> aauxv_ok m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->   (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - PARSE_STACK M ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->                                                       (* [comment removed for export] *)
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m -> arelro_lib m ->
      (1 <= N -> addressable m D N) ->                                                                  (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + PARSE_LF <= READCFG_MAXLIVE)%nat ->                                (* [comment removed for export] *)
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) PF_storenew R_parse_one_OSSL_ECHSTORE_new CH ->                                   (* [comment removed for export] *)
      parse_closed_ok M ->
      pf_ok (as_TR H) PF_biofree (bv_unsigned ra) CH ->
      PARSE_COST M <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (parse_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB LF M D N ds lo B shi m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  Definition C15_stmts : Prop := parse_one_stmt /\ fuzz_stmt H ECHL.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition R_fuzz_parse_one : Z := 0x1ef250.
  Definition R_fuzz_CRYPTO_memdup : Z := 0x1ef274.
  Definition R_fuzz_parse_one_2 : Z := 0x1ef374.
  Definition R_fuzz_CRYPTO_free : Z := 0x1ef390.
  Definition R_fuzz_ERR_clear_error : Z := 0x1ef394.
  Definition cx_dummy : ctxinfo := mkCX (0, 0, 0) 0 0.
  Definition mid_at (cph : ctxphase) (eph : errphase) : libmid := mkMID 1 cph eph errst_zero false.
  (* [comment removed for export] *)
  Definition parse_rows (cph : ctxphase) (eph : errphase) (site : Z) : list (Z * list Z) :=
       pf_shift R_parse_one_OSSL_ECHSTORE_new PF_storenew
    ++ PFC_parse (mid_at cph eph) cx_dummy
    ++ pf_shift site PF_biofree.
  Definition fuzz_rows (cph : ctxphase) (eph eph2 eph3 : errphase) : list (Z * list Z) :=
       parse_rows cph eph R_fuzz_parse_one
    ++ pf_shift R_fuzz_CRYPTO_memdup PF_cmemdup
    ++ parse_rows (CtxReady cx_dummy) eph2 R_fuzz_parse_one_2
    ++ pf_shift R_fuzz_CRYPTO_free PF_cfree
    ++ pf_shift R_fuzz_ERR_clear_error (PF_errclear eph3).
  End RC.
End W.
End HCW.

(* [comment removed for export] *)
Definition PF9newC (ph : ctxphase) : list (Z * list Z) := match ph with CtxReady x => PF_bionew_b64 x | CtxFresh => PF_bionew_b64 cx_dummy end.
Definition PF9freeC : list (Z * list Z) := PF_biofreeall.
