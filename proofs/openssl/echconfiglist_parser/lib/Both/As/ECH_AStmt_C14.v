(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsStack0 AsAuxv ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
     ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C10 ECH_AStmt_C11 ECH_AStmt_C12 ECH_AStmt_C13.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From Stdlib Require Import Sorting.Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record libmid := mkMID {
  mid_flag : Z;           (* [comment removed for export] *)
  mid_ctx : ctxphase;     (* [comment removed for export] *)
  mid_err : errphase;     (* [comment removed for export] *)
  mid_E : errst;          (* [comment removed for export] *)
  mid_vdso : bool }.      (* [comment removed for export] *)
Definition ERRPH_mid (LB : list block) (m : mem) (cph : ctxphase) (eph : errphase) : Prop :=
  match cph, eph with
  | CtxFresh, ErrFresh => ERR_fresh_core m
  | CtxFresh, ErrReady _ => False
  | CtxReady _, _ => ERRPH LB m eph
  end.
Definition VDSO_X : list (Z * Z) := [(A_vdso_func, A_vdso_func + 8)].
Definition errst_fits (E : errst) : Prop :=
  Forall (fun s => lb_bytes (blocks_slot s) <= ERRDEBUG_BYTES) (es_slots E).                 (* [comment removed for export] *)
(* [comment removed for export] *)
Definition LIBMID (LB : list block) (m : mem) (M : libmid) : Prop :=
     IMPL_mem m /\ MEMFLAG m (mid_flag M)
  /\ CTXPH LB m (mid_ctx M) /\ ERRPH_mid LB m (mid_ctx M) (mid_err M) /\ ERRX m (mid_err M) (mid_E M)
  /\ rw_cells asegs m A_vdso_func [C8 (wz (if mid_vdso M then 0 else P_cgt_init))]
  /\ m (wa A_global_cleanup) = None
  /\ errst_fits (mid_E M)
  /\ GOT_mem m /\ GOT_echfree m /\ GOT_x509vpm m /\ METH_mem m /\ METH_b64 m /\ HPKE_tabs m /\ relro_lib m
  /\ errph_shad m (mid_err M) /\ errph_below (mid_err M) aceil.                                          (* [comment removed for export] *)
Definition mid_errblocks (M : libmid) : list block := blocks_ERRST (mid_E M).
Definition mid_step (M M' : libmid) : Prop :=
     mid_flag M' = 1
  /\ (forall b, mid_ctx M = CtxReady b -> mid_ctx M' = CtxReady b)
  /\ (forall c, mid_err M = ErrReady c -> mid_err M' = ErrReady c)
  /\ (mid_vdso M = true -> mid_vdso M' = true).
Definition mid_newlib_ok (M M' : libmid) (LBN : list block) : Prop :=
  exists LA LE, Permutation LBN (LA ++ LE)
    /\ (match mid_ctx M, mid_ctx M' with CtxFresh, CtxReady b => ctxph_delta CtxFresh LA b | _, _ => LA = [] end)
    /\ (match mid_err M, mid_err M' with ErrFresh, ErrReady c => errph_delta ErrFresh LE c | _, _ => LE = [] end).
Definition mid_cnt (M : libmid) : Z := ctxph_cnt (mid_ctx M) + errph_cnt (mid_err M).
Definition mid_bytes (M : libmid) : Z := ctxph_bytes (mid_ctx M) + errph_bytes (mid_err M).
Definition mid_stack (M : libmid) : Z := Z.max (ctxph_stack (mid_ctx M)) (errph_stack (mid_err M)).
(* [comment removed for export] *)
Definition mid_LF (M : libmid) : nat := ERRPH_LF (mid_err M).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DECODE_CNT : Z := 720.
Definition DECODE_BYTES : Z := 2^17.
Definition ERRSTR_CNT : Z := 32.
Definition ERRSTR_BYTES : Z := 32 * 32.
(* [comment removed for export] *)
Definition DECODE_CUM_BYTES : Z := 2^23.
Definition DECEXTS_BYTES (rem : Z) : Z := 16 * rem + 256.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DECEXTS_CM (rem : Z) : Z := 3300 * rem + 256.
Definition DECEXTS_CF (rem : Z) : Z := 2100 * rem + 256.
(* [comment removed for export] *)
Definition READCFG_STACK (M : libmid) : Z :=
  FR_OSSL_ECHSTORE_read_echconfiglist + FR_ech_read_priv_echconfiglist + 16 + 1024 + Z.max AFS_STACK (Z.max (mid_stack M) AREALLOC_STACK).
Definition READCFG_LF : nat := 8%nat.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition READCFG_MAXLIVE : nat := 256%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition R_decexts_CRYPTO_free : Z := 0x555068.          (* [comment removed for export] *)
Definition R_decexts_CRYPTO_memdup : Z := 0x555088.
Definition R_decexts_CRYPTO_malloc : Z := 0x5550ac.        (* [comment removed for export] *)
Definition R_decexts_sk_new_null : Z := 0x555130.
Definition R_decexts_sk_push : Z := 0x55518c.
Definition R_decexts_ERR_new : Z := 0x555214.
Definition R_decexts_ERR_set_debug : Z := 0x555230.
Definition R_decexts_ERR_set_error : Z := 0x555244.
Definition R_decexts_sk_pop_free : Z := 0x555288.
Definition R_decexts_ossl_echext_free : Z := 0x55529c.
Definition R_decexts_CRYPTO_free_2 : Z := 0x5552b4.
(* [comment removed for export] *)
Definition R_fcc_X509_VERIFY_PARAM_new : Z := 0x552aa0.
Definition R_fcc_suite_check : Z := 0x552ba0.          (* [comment removed for export] *)
Definition R_fcc_ERR_new : Z := 0x552c08.      Definition R_fcc_ERR_new_2 : Z := 0x552c50.      Definition R_fcc_ERR_new_3 : Z := 0x552f1c.
Definition R_fcc_ERR_set_debug : Z := 0x552c24. Definition R_fcc_ERR_set_debug_2 : Z := 0x552c6c.
Definition R_fcc_ERR_set_error : Z := 0x552c3c. Definition R_fcc_ERR_set_error_2 : Z := 0x552c84.
Definition R_fcc_X509_VERIFY_PARAM_free : Z := 0x552c94.
Definition R_fcc_add1_host : Z := 0x552e0c.
(* [comment removed for export] *)
Definition R_readcfg_read_priv : Z := 0x553038.            (* [comment removed for export] *)
Definition R_rp_CRYPTO_zalloc : Z := 0x553200.            (* [comment removed for export] *)
Definition R_rp_CRYPTO_free_595 : Z := 0x553248.
Definition R_rp_ERR_new_595 : Z := 0x553260.   Definition R_rp_ERR_set_debug_595 : Z := 0x55327c.
Definition R_rp_ERR_new_591 : Z := 0x553290.   Definition R_rp_ERR_set_debug_591 : Z := 0x5532ac.   Definition R_rp_ERR_set_error_T1 : Z := 0x5532c4.   (* [comment removed for export] *)
Definition R_rp_CRYPTO_realloc : Z := 0x5533ec.
Definition R_rp_ERR_new_599 : Z := 0x553460.   Definition R_rp_ERR_set_debug_599 : Z := 0x55347c.   (* [comment removed for export] *)
Definition R_rp_CRYPTO_memdup_bin : Z := 0x55359c.
Definition R_rp_CRYPTO_malloc_fmt : Z := 0x5535cc.
Definition R_rp_CRYPTO_free_fmt : Z := 0x55363c.
Definition R_rp_ERR_new_603 : Z := 0x553648.   Definition R_rp_ERR_set_debug_603 : Z := 0x553664.   Definition R_rp_ERR_set_error_T2 : Z := 0x55367c.
Definition R_rp_BIO_free_all : Z := 0x55369c.
Definition R_rp_CRYPTO_free_645 : Z := 0x5536b8.  Definition R_rp_CRYPTO_free_646 : Z := 0x5536cc.
Definition R_rp_BIO_new_mem_buf : Z := 0x5536e8. Definition R_rp_BIO_new : Z := 0x5536fc.              Definition R_rp_BIO_push : Z := 0x553724.
Definition R_rp_CRYPTO_malloc_bin : Z := 0x553740. Definition R_rp_BIO_read : Z := 0x55375c.
Definition R_rp_ERR_new_631a : Z := 0x553790.  Definition R_rp_ERR_new_631 : Z := 0x5537e0.          Definition R_rp_ERR_set_debug_631 : Z := 0x5537fc.  Definition R_rp_ERR_set_error_631 : Z := 0x553814.
Definition R_rp_ERR_new_652 : Z := 0x5538a4.   Definition R_rp_ERR_set_debug_652 : Z := 0x554294.   Definition R_rp_ERR_set_error_652 : Z := 0x5542ac.
Definition R_rp_CRYPTO_zalloc_ee : Z := 0x553940.
Definition R_rp_PACKET_memdup : Z := 0x553b98.  Definition R_rp_CRYPTO_malloc_array : Z := 0x553c08.
Definition R_rp_entry_free_skip : Z := 0x553db4.
Definition R_rp_PACKET_strndup : Z := 0x553e58. Definition R_rp_decexts : Z := 0x553e80.                Definition R_rp_CRYPTO_memdup_enc : Z := 0x553ec8.
Definition R_rp_time : Z := 0x553fd4.           Definition R_rp_fcc : Z := 0x55401c.
Definition R_rp_sk_new_null : Z := 0x554054.    Definition R_rp_sk_push : Z := 0x5540b4.
Definition R_rp_entry_free_done : Z := 0x55418c.
Definition R_rp_ERR_new_534 : Z := 0x5541b8.   Definition R_rp_ERR_set_debug_534 : Z := 0x5541d4.   Definition R_rp_ERR_set_error_534 : Z := 0x5541e8.  Definition R_rp_entry_free_534 : Z := 0x5541f0.
Definition R_rp_ERR_new_538 : Z := 0x554238.   Definition R_rp_ERR_set_debug_538 : Z := 0x554254.   Definition R_rp_ERR_set_error_538 : Z := 0x554268.  Definition R_rp_entry_free_538 : Z := 0x554270.
Definition R_rp_ERR_new_637 : Z := 0x554278.   Definition R_rp_ERR_set_debug_637 : Z := 0x554294.   Definition R_rp_ERR_set_error_637 : Z := 0x5542ac.

(* [comment removed for export] *)
Definition pf_raise (r1 r2 r3 : Z) (ph : errphase) : list (Z * list Z) :=
  pf_shift r1 (PF_errnew ph) ++ pf_shift r2 PF_errdebug ++ pf_shift r3 PF_errseterr.
(* [comment removed for export] *)
Definition PF_decexts (ph : errphase) : list (Z * list Z) :=
  pf_shift R_decexts_CRYPTO_free PF_cfree ++ pf_shift R_decexts_CRYPTO_memdup PF_cmemdup ++ pf_shift R_decexts_CRYPTO_malloc PF_cmalloc
  ++ pf_shift R_decexts_sk_new_null PF_sknew_null ++ pf_shift R_decexts_sk_push PF_skpush
  ++ pf_raise R_decexts_ERR_new R_decexts_ERR_set_debug R_decexts_ERR_set_error ph
  ++ pf_shift R_decexts_sk_pop_free (PF_skpopfree PF_extfree) ++ pf_shift R_decexts_ossl_echext_free PF_extfree ++ pf_shift R_decexts_CRYPTO_free_2 PF_cfree.
(* [comment removed for export] *)
Definition PF_fcc (ph : errphase) : list (Z * list Z) :=
  pf_shift R_fcc_X509_VERIFY_PARAM_new PF_vpmnew ++ pf_shift R_fcc_suite_check (PF_suitebad ph) ++ pf_shift R_fcc_X509_VERIFY_PARAM_free PF_vpmfree ++ pf_shift R_fcc_add1_host PF_add1host
  ++ pf_raise R_fcc_ERR_new R_fcc_ERR_set_debug R_fcc_ERR_set_error ph ++ pf_raise R_fcc_ERR_new_2 R_fcc_ERR_set_debug_2 R_fcc_ERR_set_error_2 ph
  ++ pf_raise R_fcc_ERR_new_3 R_fcc_ERR_set_debug R_fcc_ERR_set_error ph.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BUF_shad (m : mem) (a n : Z) : Prop := accessible m a n.

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition mid_closed_ok (M : libmid) : Prop := errph_closed_ok H (mid_err M).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RCR : Z := as_Cm H ERRDEBUG_BYTES + as_Cf H ERRDEBUG_BYTES.
  Definition RAISE_COSTd (ph ph' : errphase) : Z :=
    as_Cm H (errph_bytes ph - errph_bytes ph' + ERRDEBUG_BYTES) + as_Cf H (errph_bytes ph - errph_bytes ph' + ERRDEBUG_BYTES).
  Definition DECEXTS_COST (M : libmid) (rem : Z) : Z := as_Cm H (DECEXTS_CM rem) + as_Cf H (DECEXTS_CF rem) + RAISE_COST H (mid_err M).   (* [comment removed for export] *)
  Definition DECEXTS_SPENT (M M' : libmid) (rem : Z) : Z := as_Cm H (DECEXTS_CM rem) + as_Cf H (DECEXTS_CF rem) + RAISE_COSTd (mid_err M) (mid_err M').   (* [comment removed for export] *)
  Definition FCC_COST (M : libmid) (ns : Z) : Z := as_Cm H VPM_SIZE + ADD1HOST_COST H + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) + RAISE_COST H (mid_err M) + ns * RCR.   (* [comment removed for export] *)
  Definition FCC_SPENT (M M' : libmid) (ns : Z) : Z := as_Cm H VPM_SIZE + ADD1HOST_COST H + as_Cf H (VPM_SIZE + ADD1HOST_BYTES) + RAISE_COSTd (mid_err M) (mid_err M') + ns * RCR.   (* [comment removed for export] *)
  Definition READCFG_COST (M : libmid) : Z := as_Cm H DECODE_CUM_BYTES + as_Cf H DECODE_CUM_BYTES + errph_cost H (mid_err M).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition DECEXTS_STACK (M : libmid) : Z := FR_ech_decode_echconfig_exts + 192 + Z.max (RAISE_STACK (mid_err M)) (Z.max SKPUSH_STACK (SKPOPFREE_STACK EXTFREE_STACK)).
  Definition decexts_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LIB LB : list block) (LF : list fframe) (M : libmid) (ee pk base len cur rem : Z) (E : entrep) (bs : list byte) (lo B : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (rv : Z) (M' : libmid)
                    (xs : option (skrep * list extrep)) (exp : Z) (NB LBN : list block) (cur' rem' : Z) (XS : list (Z * Z)),
      let LB' := NB ++ LBN ++ LB in
      let E' := mkENT (en_version E) (en_pname E) (en_pname_o E) (en_publen E) (en_pub E) (en_pub_o E) (en_nsuites E) (en_suites E) (en_suites_o E)
                      (en_maxname E) (en_cfgid E) exp xs (en_loadtime E) (en_forretry E) (en_enclen E) (en_encoded E) (en_encoded_o E) (en_id E) in
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ stack0 m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M /\ mid_vdso M' = mid_vdso M
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES
      /\ ENTRYobj LB' m' ee E' /\ ENTRY_shad m' ee E' /\ Permutation (blocks_EXTS exp xs) NB
      /\ ((rv = 1 /\ xs <> None /\ rem' = 0) \/ (rv = 0 /\ xs = None /\ exp = 0 /\ NB = []))
      /\ 5 * Z.of_nat (length NB) <= 2 * (rem - rem') + 10 /\ lb_bytes NB <= rem + SK_SIZE + 8 * (rem + 4)
      /\ rw_cells asegs m' pk (pk_cells cur' base rem') /\ bytes_at asegs m' base bs /\ BUF_shad m' base len /\ pk_in base len cur' rem' /\ cur + rem = cur' + rem'
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m' /\ athr_cells m'                                                     (* [comment removed for export] *)
      /\ xpres H LB (bv_unsigned sp) (XS ++ (pk, pk + 24) :: (ee, ee + ENTRY_SIZE) :: ERR_XE ++ errph_foot (mid_err M)) m m'   (* [comment removed for export] *)
      /\ as_AL H s' >= as_AL H s - DECEXTS_SPENT M M' rem.                                                           (* [comment removed for export] *)
  Definition decexts_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
           (M : libmid) (x : ctxinfo) (ee pk base len cur rem lo B : Z) (E : entrep) (bs : list byte) (pbin : bptr) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_ech_decode_echconfig_exts) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 ee -> a1 = Z_to_bv 64 pk ->
      ENTRYobj LB m ee E -> en_exts E = 0 -> en_exts_o E = None -> Forall (fun b => blk_addr b + blk_size b <= lo) (blocks_ENTRY ee E) ->
      ENTRY_shad m ee E ->                                                                                          (* [comment removed for export] *)
      rw_cells asegs m pk (pk_cells cur base rem) -> pk_in base len cur rem -> 1 <= rem -> rem <= 1499 ->
      bv_unsigned sp <= pk -> pk + 24 <= B -> pk mod 8 = 0 -> accessible m pk 24 -> offchain CH pk 24 ->          (* [comment removed for export] *)
      In (pbin, base, len) LB -> en_id E <> pbin -> bytes_at asegs m base bs -> zlength bs <= len -> cur + rem <= base + zlength bs ->
      BUF_shad m base len ->                                                                                        (* [comment removed for export] *)
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' (blocks_ENTRY ee E) -> blk_id b <> blk_id b') ->
      (forall b, In b LIB -> blk_id b <> pbin) ->
      as_RHEAP H s (mid_errblocks M ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (mid_errblocks M ++ LB) + errph_bytes (mid_err M) + DECEXTS_BYTES rem + ERRDEBUG_BYTES <= as_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + errph_cnt (mid_err M) + (2 * rem) / 5 + 8 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - DECEXTS_STACK M -> stack0 m lo (bv_unsigned sp) ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      mid_closed_ok M ->                                                                                            (* [comment removed for export] *)
      as_RFS H LF m -> (length LF + mid_LF M <= AFS_MAXLIVE)%nat -> athr_cells m ->                                 (* [comment removed for export] *)
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_decexts (mid_err M)) (bv_unsigned ra) CH -> DECEXTS_COST M rem <= as_AL H s ->            (* [comment removed for export] *)
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (decexts_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB LF M ee pk base len cur rem E bs lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint suite_cells (rows : list (Z * Z * Z)) : list cell :=
    match rows with [] => [] | (kem, kdf, aead) :: rows' => C2 (wz kem) :: C2 (wz kdf) :: C2 (wz aead) :: suite_cells rows' end.
  Definition row_ok (r : Z * Z * Z) : Prop := 0 <= fst (fst r) < 2^16 /\ 0 <= snd (fst r) < 2^16 /\ 0 <= snd r < 2^16.

  (* [comment removed for export] *)
  Definition FCC_CNT : Z := 5.
  Definition FCC_BYTES : Z := VPM_SIZE + 16 + 264 + SK_SIZE + 32.
  Definition FCC_ICPT_STACK : Z := 8192.   (* [comment removed for export] *)
  Definition FCC_STACK (M : libmid) : Z := FR_ech_final_config_checks + Z.max (Z.max ADD1HOST_STACK (Z.max VPMNEW_STACK VPMFREE_STACK)) (Z.max (SUITECHECK_STACK (mid_err M)) FCC_ICPT_STACK).   (* [comment removed for export] *)
  Definition fcc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LIB LB : list block) (LF : list fframe) (M : libmid) (ee : Z) (E : entrep) (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (rv : Z) (M' : libmid) (LBN : list block) (XS : list (Z * Z)),
      let LB' := LBN ++ LB in
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ (rv = 0 \/ rv = 1)
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ stack0 m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M /\ mid_vdso M' = mid_vdso M
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES
      /\ ENTRYobj LB' m' ee E /\ ENTRY_shad m' ee E
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m' /\ athr_cells m'                                                     (* [comment removed for export] *)
      /\ xpres H LB (bv_unsigned sp) (XS ++ ERR_XE ++ errph_foot (mid_err M)) m m'                                    (* [comment removed for export] *)
      /\ as_AL H s' >= as_AL H s - FCC_SPENT M M' (en_nsuites E).                                                    (* [comment removed for export] *)
  Definition fcc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
           (M : libmid) (x : ctxinfo) (ee lo B : Z) (E : entrep) (errv : word) (CH : list (Z * Z))
           (rows : list (Z * Z * Z)) (ps : bptr) (sn : Z) (pn : bptr) (ns slack : list byte),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_ech_final_config_checks) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 ee -> ENTRYobj LB m ee E -> 1 <= en_nsuites E < 2^31 ->
      en_suites_o E = Some (ps, sn) -> rw_cells asegs m (en_suites E) (suite_cells rows) -> zlength rows = en_nsuites E -> 6 * en_nsuites E <= sn ->
      Forall row_ok rows ->
      en_pname_o E = Some (pn, zlength ns + 1) -> bytes_at asegs m (en_pname E) (ns ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) ns -> 1 <= zlength ns <= 255 ->
      (- (en_pname E + zlength ns + 1)) mod 8 <= zlength slack ->                                                   (* [comment removed for export] *)
      Forall (fun b => blk_addr b + blk_size b <= lo) (blocks_ENTRY ee E) ->
      ENTRY_shad m ee E ->                                                                                          (* [comment removed for export] *)
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' (blocks_ENTRY ee E) -> blk_id b <> blk_id b') ->
      as_RHEAP H s (mid_errblocks M ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (mid_errblocks M ++ LB) + errph_bytes (mid_err M) + FCC_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + errph_cnt (mid_err M) + FCC_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - FCC_STACK M -> stack0 m lo (bv_unsigned sp) ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      mid_closed_ok M ->
      as_RFS H LF m -> (length LF + mid_LF M <= AFS_MAXLIVE)%nat -> athr_cells m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_fcc (mid_err M)) (bv_unsigned ra) CH -> FCC_COST M (en_nsuites E) <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (fcc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB LF M ee E lo B m mo) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section RC.
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).     (* [comment removed for export] *)
  Definition PF_entry (M : libmid) : list (Z * list Z) :=                                 (* [comment removed for export] *)
    pf_shift R_rp_CRYPTO_zalloc_ee PF_czalloc ++ pf_shift R_rp_PACKET_memdup PF_pkmemdup ++ pf_shift R_rp_CRYPTO_malloc_array PF_cmalloc   (* [comment removed for export] *)
    ++ pf_shift R_rp_entry_free_skip PF_entryfree ++ pf_shift R_rp_PACKET_strndup PF_pkstrndup ++ pf_shift R_rp_decexts (PF_decexts (mid_err M))
    ++ pf_shift R_rp_CRYPTO_memdup_enc PF_cmemdup ++ pf_shift R_rp_fcc (PF_fcc (mid_err M))
    ++ pf_shift R_rp_sk_new_null PF_sknew_null ++ pf_shift R_rp_sk_push PF_skpush
    ++ pf_shift R_rp_entry_free_done PF_entryfree ++ pf_shift R_rp_entry_free_534 PF_entryfree ++ pf_shift R_rp_entry_free_538 PF_entryfree
    ++ pf_raise R_rp_ERR_new_534 R_rp_ERR_set_debug_534 R_rp_ERR_set_error_534 (mid_err M)
    ++ pf_raise R_rp_ERR_new_538 R_rp_ERR_set_debug_538 R_rp_ERR_set_error_538 (mid_err M)
    ++ pf_raise R_rp_ERR_new_637 R_rp_ERR_set_debug_637 R_rp_ERR_set_error_637 (mid_err M).
  Definition PF_read_priv (M : libmid) : list (Z * list Z) :=
    pf_shift R_rp_CRYPTO_zalloc PF_czalloc ++ pf_shift R_rp_CRYPTO_realloc PF_crealloc ++ pf_shift R_rp_CRYPTO_free_595 PF_cfree
    ++ pf_raise R_rp_ERR_new_595 R_rp_ERR_set_debug_595 R_rp_ERR_set_error_T1 (mid_err M) ++ pf_raise R_rp_ERR_new_591 R_rp_ERR_set_debug_591 R_rp_ERR_set_error_T1 (mid_err M)
    ++ pf_raise R_rp_ERR_new_599 R_rp_ERR_set_debug_599 R_rp_ERR_set_error_T2 (mid_err M)
    ++ pf_shift R_rp_CRYPTO_memdup_bin PF_cmemdup ++ pf_shift R_rp_CRYPTO_malloc_fmt PF_cmalloc ++ pf_shift R_rp_CRYPTO_free_fmt PF_cfree
    ++ pf_raise R_rp_ERR_new_603 R_rp_ERR_set_debug_603 R_rp_ERR_set_error_T2 (mid_err M)
    ++ pf_shift R_rp_BIO_new_mem_buf (PF_newmembuf (mid_ctx M)) ++ pf_shift R_rp_BIO_new (PF9new (mid_ctx M)) ++ pf_shift R_rp_CRYPTO_malloc_bin PF_cmalloc
    ++ pf_raise R_rp_ERR_new_631 R_rp_ERR_set_debug_631 R_rp_ERR_set_error_631 (mid_err M) ++ pf_shift R_rp_ERR_new_631a (PF_errnew (mid_err M))
    ++ pf_raise R_rp_ERR_new_652 R_rp_ERR_set_debug_652 R_rp_ERR_set_error_652 (mid_err M)
    ++ PF_entry M
    ++ pf_shift R_rp_BIO_free_all PF9free ++ pf_shift R_rp_CRYPTO_free_645 PF_cfree ++ pf_shift R_rp_CRYPTO_free_646 PF_cfree.
  Definition PF_readcfg (M : libmid) : list (Z * list Z) := PF_read_priv M.    (* [comment removed for export] *)

  Definition readcfg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LIB LB : list block) (LF : list fframe) (M : libmid) (st : Z) (S : storerep) (mb : Z) (R : membio) (ds : list byte)
      (lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun k => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (rv : Z)
                    (M' : libmid) (S' : storerep) (R' : membio) (LBN NB : list block) (XS : list (Z * Z)),
      let LB' := NB ++ LBN ++ LB in
      as_VIS H s' (cfg_ms k) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ (rv = 0 \/ rv = 1)
      /\ as_AKREL H s' k /\ as_MPRES H mo (cfg_model k)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp) /\ stack0 m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' (mid_errblocks M' ++ LB') m'
      /\ LIBMID (LBN ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LBN /\ mid_ctx M' = mid_ctx M
      /\ STOREobj LB' m' st S' /\ STORE_shad m' st S' /\ es_id S' = es_id S /\ Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB)
      /\ Z.of_nat (length NB) <= DECODE_CNT /\ lb_bytes NB <= DECODE_BYTES
      /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES
      /\ List.NoDup (map blk_id (blocks_STORE st S'))
      /\ MEMBIO H LB' m' mb R' /\ MEMBIO_shad m' mb R' /\ blocks_MEMBIO mb R' = blocks_MEMBIO mb R /\ bytes_at asegs m' (mb_buf R) ds
      /\ Forall (fs_scratch H LF) XS /\ as_RFS H LF m' /\ athr_cells m'                                                     (* [comment removed for export] *)
      /\ xpres H LB (bv_unsigned sp) (XS ++ [(st, st + STORE_SIZE)] ++ MEMBIO_foot mb R ++ ERR_XE ++ VDSO_X ++ errph_foot (mid_err M)) m m'   (* [comment removed for export] *)
      /\ as_AL H s' >= as_AL H s - READCFG_COST M.
  Definition readcfg_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
           (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 st -> a1 = Z_to_bv 64 mb ->
      STOREobj LB m st S -> es_entries S = 0 -> es_entries_o S = None -> st + STORE_SIZE <= lo -> STORE_shad m st S ->
      MEMBIO H LB m mb R -> mb_pos R = 0 -> mb_nread R = 0 -> MEMBIO_below mb R lo -> MEMBIO_sep mb R -> MEMBIO_shad m mb R -> PAYLOAD_shad m R ->
      bytes_at asegs m (mb_buf R) ds -> zlength ds = mb_len R ->
      (1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD) ->
      (1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S) ->
      List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)) ->
      LIBMID LIB m M -> (forall b, In b LIB -> In b LB) -> mid_ctx M = CtxReady x -> mid_flag M = 1 ->
      (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b') ->
      as_RHEAP H s (mid_errblocks M ++ LB) m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> aauxv_ok m B -> bv_unsigned sp <= B -> B < 2^64 -> bv_unsigned sp mod 16 = 0 ->   (* [comment removed for export] *)
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - READCFG_STACK M -> stack0 m lo (bv_unsigned sp) ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
      mid_closed_ok M ->
      as_RFS H LF m -> (length LF + READCFG_LF <= READCFG_MAXLIVE)%nat -> athr_cells m ->                             (* [comment removed for export] *)
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) (PF_readcfg M) (bv_unsigned ra) CH -> READCFG_COST M <= as_AL H s ->
      bv_unsigned ra mod 2 = 0 ->
      as_SR H (readcfg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LIB LB LF M st S mb R ds lo B m mo) (mkCfg msF mo).
  End RC.

  Definition C14_stmts (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)) : Prop :=
    readcfg_stmt PF9new PF9free /\ fcc_stmt /\ decexts_stmt.
End W.
End HCW.
